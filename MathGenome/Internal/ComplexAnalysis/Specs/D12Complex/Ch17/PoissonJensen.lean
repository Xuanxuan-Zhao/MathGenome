import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch07.Meromorphic
import Mathlib.Analysis.Meromorphic.Divisor
import Mathlib.Analysis.Complex.Poisson

/-! Poisson–Jensen, paper.tex:2859–2891. The meromorphic function is the
canonical scalar sphere-valued function. Natural-number weights give the
repeated local multiplicities; no divisor factorization is assumed. -/
noncomputable section
open Complex Metric Set
open scoped ComplexConjugate

namespace D12Complex.PoissonJensen

def green (R : ℝ) (z a : ℂ) : ℝ :=
  Real.log ‖((R : ℂ) ^ 2 - conj a * z) / ((R : ℂ) * (z - a))‖

def diskDivisor (F : ℂ → RiemannSphere) (R : ℝ) :=
  MeromorphicOn.divisor (scalarFinitePart F) (closedBall 0 R)

def zeroMultiplicity (F : ℂ → RiemannSphere) (R : ℝ) (a : ℂ) : ℕ :=
  (diskDivisor F R a).toNat

def poleMultiplicity (F : ℂ → RiemannSphere) (R : ℝ) (a : ℂ) : ℕ :=
  (-diskDivisor F R a).toNat

/-- Exactly the source angular integral, using circleMap for R exp(it). -/
def boundaryPoisson (F : ℂ → RiemannSphere) (R : ℝ) (z : ℂ) : ℝ :=
  (2 * Real.pi)⁻¹ * ∫ t in (0 : ℝ)..2 * Real.pi,
    ((circleMap 0 R t + z) / (circleMap 0 R t - z)).re *
      Real.log ‖scalarFinitePart F (circleMap 0 R t)‖

def boundaryMean (F : ℂ → RiemannSphere) (R : ℝ) : ℝ :=
  (2 * Real.pi)⁻¹ * ∫ t in (0 : ℝ)..2 * Real.pi,
    Real.log ‖scalarFinitePart F (circleMap 0 R t)‖

end D12Complex.PoissonJensen

namespace Specs.D12Complex.Ch17.PoissonJensen
open _root_.D12Complex _root_.D12Complex.PoissonJensen

/-- Finiteness and the exact signed local orders establish the interpretation
of both weighted sums as the complete interior divisor, with multiplicity. -/
def finite_divisor_type : Prop :=
  ∀ (U : Set ℂ) (F : ℂ → RiemannSphere) (R : ℝ),
    ScalarMeromorphicOn U F → 0 < R → closedBall 0 R ⊆ U →
    (∀ ζ ∈ sphere (0 : ℂ) R, F ζ ≠ sphereInfty ∧ F ζ ≠ sphereFinite 0) →
    (Function.support (zeroMultiplicity F R)).Finite ∧
    (Function.support (poleMultiplicity F R)).Finite ∧
    Function.support (zeroMultiplicity F R) ⊆ ball 0 R ∧
    Function.support (poleMultiplicity F R) ⊆ ball 0 R ∧
    ∀ a ∈ closedBall (0 : ℂ) R,
      scalarSignedOrder F a = some (diskDivisor F R a) ∧
      (0 < zeroMultiplicity F R a ↔ F a = sphereFinite 0) ∧
      (0 < poleMultiplicity F R a ↔ F a = sphereInfty)

/-- Both angular integrals exist as ordinary scalar integrals. -/
def integrands_integrable_type : Prop :=
  ∀ (U : Set ℂ) (F : ℂ → RiemannSphere) (R : ℝ),
    ScalarMeromorphicOn U F → 0 < R → closedBall 0 R ⊆ U →
    (∀ ζ ∈ sphere (0 : ℂ) R, F ζ ≠ sphereInfty ∧ F ζ ≠ sphereFinite 0) →
    IntervalIntegrable (fun t => Real.log ‖scalarFinitePart F (circleMap 0 R t)‖)
      MeasureTheory.volume 0 (2 * Real.pi) ∧
    ∀ z ∈ ball (0 : ℂ) R,
      IntervalIntegrable (fun t =>
        ((circleMap 0 R t + z) / (circleMap 0 R t - z)).re *
          Real.log ‖scalarFinitePart F (circleMap 0 R t)‖)
        MeasureTheory.volume 0 (2 * Real.pi)

def poisson_jensen_type : Prop :=
  ∀ (U : Set ℂ) (F : ℂ → RiemannSphere) (R : ℝ),
    ScalarMeromorphicOn U F → 0 < R → closedBall 0 R ⊆ U →
    (∀ ζ ∈ sphere (0 : ℂ) R, F ζ ≠ sphereInfty ∧ F ζ ≠ sphereFinite 0) →
    ∀ z ∈ ball (0 : ℂ) R, F z ≠ sphereInfty → F z ≠ sphereFinite 0 →
      Real.log ‖scalarFinitePart F z‖ = boundaryPoisson F R z -
        (∑ᶠ a : ℂ, (zeroMultiplicity F R a : ℝ) * green R z a) +
        (∑ᶠ b : ℂ, (poleMultiplicity F R b : ℝ) * green R z b)

def jensen_type : Prop :=
  ∀ (U : Set ℂ) (F : ℂ → RiemannSphere) (R : ℝ),
    ScalarMeromorphicOn U F → 0 < R → closedBall 0 R ⊆ U →
    (∀ ζ ∈ sphere (0 : ℂ) R, F ζ ≠ sphereInfty ∧ F ζ ≠ sphereFinite 0) →
    F 0 ≠ sphereInfty → F 0 ≠ sphereFinite 0 →
      boundaryMean F R = Real.log ‖scalarFinitePart F 0‖ +
        (∑ᶠ a : ℂ, (zeroMultiplicity F R a : ℝ) * Real.log (R / ‖a‖)) -
        (∑ᶠ b : ℂ, (poleMultiplicity F R b : ℝ) * Real.log (R / ‖b‖))

end Specs.D12Complex.Ch17.PoissonJensen
