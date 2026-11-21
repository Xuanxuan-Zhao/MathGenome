import MathGenome.Internal.ODEDynamics.Specs.D13Unified.Ch16.HopfReturnExpansion

/-! The geometric part of paper.tex:3717–3721.  All orbits below are traces
of complete physical-time solutions.  No orbit or global flow is assumed. -/
noncomputable section
namespace Specs.D13Unified.Ch16.HopfPeriodicOrbitBridge

open Complex Filter Set
open CubicHomologicalElimination CubicNormalForm HopfReturnExpansion

/-- The source assumptions needed for geometry; the scalar crossing and cubic
nondegeneracy assumptions are unnecessary for this component. -/
def SourceHypotheses (F : ℝ × ℂ → ℂ) (ω : ℝ) : Prop :=
  ContDiffAt ℝ 5 F (0, 0) ∧ 0 < ω ∧
  Module.End.HasEigenvalue (complexifiedLinearization F 0).toLin' (eigenvalue 0 ω) ∧
  (∀ᶠ μ in nhds (0 : ℝ), F (μ, 0) = 0)

/-- Exactly the data delivered by the authorized return-expansion theorem. -/
def ReturnData (F : ℝ × ℂ → ℂ) (ω ε ρ δ C : ℝ) (P Q : ℝ × ℝ → ℝ) : Prop :=
  0 < ε ∧ 0 < ρ ∧ 0 < δ ∧ 0 < C ∧ δ < ρ ∧
  CoordinateValidity F ε ρ ∧
  ContDiffOn ℝ 2 P (returnBox δ ε) ∧
  ContDiffOn ℝ 2 Q (returnBox δ ε) ∧
  ContDiffOn ℝ 1 (returnError F P) (returnBox δ ε) ∧
  (∀ μ : ℝ, |μ| < ε → P (0, μ) = 0 ∧ Q (0, μ) = linearReturnFactor F μ - 1) ∧
  (∀ q ∈ returnBox δ ε,
    P q = q.1 * (1 + Q q) ∧ |returnError F P q| ≤ C * |q.1| ^ 4 ∧
    |deriv (fun r => returnError F P (r, q.2)) q.1| ≤ C * |q.1| ^ 3 ∧
    |deriv (fun μ => returnError F P (q.1, μ)) q.2| ≤ C * |q.1| ^ 4) ∧
  (∀ μ r : ℝ, |μ| < ε → 0 < r → r < δ →
    FullAngularTurn F ω μ r (P (r, μ)) ρ)

/-- A positive period, actual equation at every real time, and nonconstancy.
Repeated periods and phase shifts are permitted. -/
def IsPeriodicSolution (V : ℂ → ℂ) (z : ℝ → ℂ) (T : ℝ) : Prop :=
  0 < T ∧ Function.Periodic z T ∧
  (∀ t : ℝ, HasDerivAt z (V (z t)) t) ∧ ∃ s t : ℝ, z s ≠ z t

def IsPeriodicOrbit (V : ℂ → ℂ) (Γ : Set ℂ) : Prop :=
  ∃ (z : ℝ → ℂ) (T : ℝ), IsPeriodicSolution V z T ∧ range z = Γ

/-- Only points in the finite itinerary are required to stay in the local
return domain.  Invariance of an entire interval is not a premise. -/
def NoHigherReturnCycles (P : ℝ × ℝ → ℝ) (d η : ℝ) : Prop :=
  ∀ μ : ℝ, |μ| < η →
    StrictMonoOn (fun r => P (r, μ)) (Ioo 0 d) ∧
    ∀ (r : ℝ) (n : ℕ), 0 < n →
      (∀ j ≤ n, (fun s => P (s, μ))^[j] r ∈ Ioo 0 d) →
      (fun s => P (s, μ))^[n] r = r → P (r, μ) = r

/-- A physical periodic solution, with a finite list of successive first-ray
crossings.  The winding is positive and integral, not assumed to be one.
The last clause identifies each physical segment with a genuine angular turn. -/
def PeriodicItinerary (F : ℝ × ℂ → ℂ) (ω μ : ℝ)
    (P : ℝ × ℝ → ℝ) (d ρ : ℝ) (Γ : Set ℂ) : Prop :=
  ∃ (z : ℝ → ℂ) (T : ℝ) (n : ℕ) (times radii : ℕ → ℝ) (angle : ℝ → ℝ),
    IsPeriodicSolution (fun w => transformedField F (μ, w)) z T ∧ range z = Γ ∧
    0 < n ∧ times 0 = 0 ∧ times n = T ∧
    StrictMonoOn times (Icc 0 n) ∧ angle 0 = 0 ∧ angle T = turnAngle * n ∧
    StrictMonoOn angle (Icc 0 T) ∧
    (∀ t ∈ Icc 0 T, 0 < ‖z t‖ ∧
      z t = polarPoint ‖z t‖ (angle t) ∧
      HasDerivWithinAt angle (angularVelocity F (angle t) ‖z t‖ μ) (Icc 0 T) t) ∧
    (∀ j ≤ n, 0 < radii j ∧ radii j < d ∧ z (times j) = (radii j : ℂ) ∧
      angle (times j) = turnAngle * j) ∧
    radii n = radii 0 ∧
    ∀ j < n, radii (j + 1) = P (radii j, μ) ∧
      FirstAngularTurn F μ (radii j) (radii (j + 1)) ∧
      ∃ (u clock : ℝ → ℝ) (v : ℝ → ℂ),
        u 0 = radii j ∧ u turnAngle = radii (j + 1) ∧ clock 0 = 0 ∧
        clock turnAngle = times (j + 1) - times j ∧
        (∀ θ ∈ Icc 0 turnAngle, v (clock θ) = polarPoint (u θ) θ) ∧
        (∀ t ∈ Icc 0 (times (j + 1) - times j),
          v t = z (times j + t) ∧ ‖v t‖ < ρ ∧
          HasDerivWithinAt v (transformedField F (μ, v t))
            (Icc 0 (times (j + 1) - times j)) t)

/-- Uniform geometric bridge, for ANY prescribed smaller return and parameter
cutoffs.  σ is the ball for contained orbits; τ is the smaller starting radius
whose full cycles are confined there.  U and all scales are parameter independent.
The single actual coordinate chart also explicitly lifts original solutions. -/
def GeometricBridge : Prop :=
  ∀ (F : ℝ × ℂ → ℂ) (ω : ℝ), SourceHypotheses F ω →
  ∀ (ε ρ δ C : ℝ) (P Q : ℝ × ℝ → ℝ), ReturnData F ω ε ρ δ C P Q →
  ∀ (d η : ℝ), 0 < d → d ≤ δ → 0 < η → η ≤ ε →
    ∃ ε₀ > 0, ∃ σ > 0, ∃ τ > 0, ∃ U : Set ℂ,
      ε₀ ≤ η ∧ σ < d ∧ σ < ρ ∧ τ < σ ∧ IsOpen U ∧ (0 : ℂ) ∈ U ∧
      NoHigherReturnCycles P σ ε₀ ∧
      (∃ e : OpenPartialHomeomorph (ℝ × ℂ) (ℝ × ℂ),
        (e : ℝ × ℂ → ℝ × ℂ) = familyCoordinate F ∧
        stateParameterBox ε₀ σ ⊆ e.source ∧
        (∀ μ x, |μ| < ε₀ → x ∈ U →
          (μ, x) ∈ e.target ∧ (e.symm (μ, x)).1 = μ ∧ ‖(e.symm (μ, x)).2‖ < σ) ∧
        (∀ μ : ℝ, |μ| < ε₀ →
          ∀ Γ : Set ℂ, IsPeriodicOrbit (fun x => F (μ, x)) Γ → Γ ⊆ U →
            ∃ (z : ℝ → ℂ) (T : ℝ),
              IsPeriodicSolution (fun x => F (μ, x)) z T ∧ range z = Γ ∧
              IsPeriodicSolution (fun w => transformedField F (μ, w))
                (fun t => (e.symm (μ, z t)).2) T ∧
              (∀ t : ℝ, ‖(e.symm (μ, z t)).2‖ < σ ∧
                coordinate F μ (e.symm (μ, z t)).2 = z t) ∧
              Γ = coordinate F μ '' range (fun t => (e.symm (μ, z t)).2))) ∧
      (∀ μ : ℝ, |μ| < ε₀ →
        (∀ Γ : Set ℂ,
          IsPeriodicOrbit (fun w => transformedField F (μ, w)) Γ →
          Γ ⊆ Metric.ball 0 σ →
          PeriodicItinerary F ω μ P σ ρ Γ ∧
          ∃ r : ℝ, 0 < r ∧ r < d ∧ (r : ℂ) ∈ Γ ∧ P (r, μ) = r) ∧
        (∀ r : ℝ, 0 < r → r < τ → P (r, μ) = r →
          ∃ Γ : Set ℂ, IsPeriodicOrbit (fun w => transformedField F (μ, w)) Γ ∧
            (r : ℂ) ∈ Γ ∧ Γ ⊆ Metric.ball 0 σ ∧
            IsPeriodicOrbit (fun x => F (μ, x)) (coordinate F μ '' Γ) ∧
            coordinate F μ '' Γ ⊆ U) ∧
        (∀ Γ Λ : Set ℂ,
          IsPeriodicOrbit (fun w => transformedField F (μ, w)) Γ →
          IsPeriodicOrbit (fun w => transformedField F (μ, w)) Λ →
          Γ ⊆ Metric.ball 0 σ → Λ ⊆ Metric.ball 0 σ →
          ∀ r : ℝ, 0 < r → (r : ℂ) ∈ Γ → (r : ℂ) ∈ Λ → Γ = Λ))

/-- Independent sub-obligation: the actual return is increasing after shrinking
both scales. No crossing or cubic nondegeneracy is required. -/
def LocalMonotonicity : Prop :=
  ∀ (F : ℝ × ℂ → ℂ) (ω : ℝ), SourceHypotheses F ω →
  ∀ (ε ρ δ C : ℝ) (P Q : ℝ × ℝ → ℝ), ReturnData F ω ε ρ δ C P Q →
    ∃ d > 0, ∃ η > 0, d ≤ δ ∧ η ≤ ε ∧ NoHigherReturnCycles P d η

/-- Uniform orbit uniqueness and exclusion of the zero equilibrium from every
nonconstant confined periodic trace. -/
def LocalOrbitUniqueness : Prop :=
  ∀ (F : ℝ × ℂ → ℂ) (ω : ℝ), SourceHypotheses F ω →
    ∃ ε > 0, ∃ σ > 0, ∀ μ : ℝ, |μ| < ε →
      (∀ Γ : Set ℂ, IsPeriodicOrbit (fun w => transformedField F (μ, w)) Γ →
        Γ ⊆ Metric.ball 0 σ → (0 : ℂ) ∉ Γ) ∧
      (∀ Γ Λ : Set ℂ,
        IsPeriodicOrbit (fun w => transformedField F (μ, w)) Γ →
        IsPeriodicOrbit (fun w => transformedField F (μ, w)) Λ →
        Γ ⊆ Metric.ball 0 σ → Λ ⊆ Metric.ball 0 σ →
        (Γ ∩ Λ).Nonempty → Γ = Λ)

/-- Closing an actual full turn constructs a complete nonconstant orbit, without
assuming a preexisting periodic orbit or a global flow. -/
def FixedTurnPeriodic : Prop :=
  ∀ (F : ℝ × ℂ → ℂ) (ω μ r ρ : ℝ), 0 < r →
    FullAngularTurn F ω μ r r ρ →
    ∃ Γ : Set ℂ, IsPeriodicOrbit (fun w => transformedField F (μ, w)) Γ ∧
      (r : ℂ) ∈ Γ ∧ Γ ⊆ Metric.ball 0 ρ

/-- Confined periodic trajectories have genuine physical phase lifts with
strictly positive integral winding; their period need not be a single turn. -/
def PositivePhaseLift : Prop :=
  ∀ (F : ℝ × ℂ → ℂ) (ω : ℝ), SourceHypotheses F ω →
    ∃ ε > 0, ∃ σ > 0, ∀ μ : ℝ, |μ| < ε →
      ∀ (z : ℝ → ℂ) (T : ℝ),
        IsPeriodicSolution (fun w => transformedField F (μ, w)) z T →
        (∀ t, ‖z t‖ < σ) →
        ∃ L : ℝ → ℂ, Continuous L ∧ (∀ t, Complex.exp (L t) = z t) ∧
          StrictMono (fun t => (L t).im) ∧
          (∀ t, HasDerivAt (fun s => (L s).im)
            (angularVelocity F (L t).im ‖z t‖ μ) t) ∧
          ∃ n : ℤ, 0 < n ∧ (L T).im - (L 0).im = turnAngle * n

/-- Every nonconstant confined periodic orbit meets the positive real section. -/
def ContainedSection : Prop :=
  ∀ (F : ℝ × ℂ → ℂ) (ω : ℝ), SourceHypotheses F ω →
    ∃ ε > 0, ∃ σ > 0, ∀ μ : ℝ, |μ| < ε →
      ∀ Γ : Set ℂ, IsPeriodicOrbit (fun w => transformedField F (μ, w)) Γ →
        Γ ⊆ Metric.ball 0 σ → ∃ r : ℝ, 0 < r ∧ r < σ ∧ (r : ℂ) ∈ Γ


/-- Uniformly small initial radii admit an actual first angular turn confined
in any prescribed positive normal ball. No return fixed point is assumed. -/
def UniformSmallTurns : Prop :=
  ∀ (F : ℝ × ℂ → ℂ) (ω : ℝ), SourceHypotheses F ω →
    ∀ κ : ℝ, 0 < κ →
      ∃ η > 0, ∃ τ > 0, ∀ μ r : ℝ, |μ| < η → 0 < r → r < τ →
        ∃ p : ℝ, FullAngularTurn F ω μ r p κ

/-- Every confined physical periodic orbit has the full finite itinerary for
any actual return data, uniformly after shrinking the source neighborhood. -/
def ContainedItineraries : Prop :=
  ∀ (F : ℝ × ℂ → ℂ) (ω : ℝ), SourceHypotheses F ω →
    ∃ ε₁ > 0, ∃ σ₁ > 0,
      ∀ (ε ρ δ C : ℝ) (P Q : ℝ × ℝ → ℝ), ReturnData F ω ε ρ δ C P Q →
      ∀ (μ σ : ℝ), |μ| < ε₁ → |μ| < ε → 0 < σ → σ ≤ σ₁ → σ ≤ δ →
      ∀ Γ : Set ℂ,
        IsPeriodicOrbit (fun w => transformedField F (μ, w)) Γ →
        Γ ⊆ Metric.ball 0 σ → PeriodicItinerary F ω μ P σ ρ Γ

end Specs.D13Unified.Ch16.HopfPeriodicOrbitBridge
