import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch15.PolygonRepresentation
import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch03.AbsolutelyContinuousContours
import Mathlib.Algebra.Polynomial.Basic

/-! Rational tagged sums for the actual oriented, integer-weighted cycle.
The Stieltjes increments are the oriented chords. On an affine segment they
are exactly the segment derivative times the parameter-cell length.
The denominator condition below locates every possible finite pole, including
before cancellation, on the active trace. -/
noncomputable section
open Set
open scoped BigOperators

namespace D12Complex.RationalRiemannSums

abbrev PathSampling (γ : PiecewiseC1Path) :=
  Σ P : Stieltjes.Partition γ.path.a γ.path.b, Stieltjes.Tags P

abbrev CycleSampling (Γ : IntegralCycle) :=
  ∀ γ : {γ : PiecewiseC1Path // γ ∈ Γ.chain.support}, PathSampling γ.val

def pathSum (γ : PiecewiseC1Path) (s : PathSampling γ) (f : ℂ → ℂ) (z : ℂ) : ℂ :=
  Stieltjes.taggedSum s.1 s.2 (fun t => f (γ t) / (γ t - z)) γ

def cycleSum (Γ : IntegralCycle) (s : CycleSampling Γ) (f : ℂ → ℂ) (z : ℂ) : ℂ :=
  (2 * Real.pi * Complex.I : ℂ)⁻¹ *
    ∑ γ : {γ : PiecewiseC1Path // γ ∈ Γ.chain.support},
      (Γ.chain γ.val : ℂ) * pathSum γ.val (s γ) f z

def cauchyTransform (Γ : IntegralCycle) (f : ℂ → ℂ) (z : ℂ) : ℂ :=
  (2 * Real.pi * Complex.I : ℂ)⁻¹ *
    Γ.integral (fun w => f w / (w - z))

end D12Complex.RationalRiemannSums

namespace Specs.D12Complex.Ch15.RationalRiemannSums
open _root_.D12Complex _root_.D12Complex.RationalRiemannSums
open _root_.D12Complex.PolygonRepresentation

/-- One mesh size works for every point of K and every choice of tags.
This stronger path version includes each oriented polygonal segment. -/
def uniform_path_sums_type : Prop :=
  ∀ (K : Set ℂ) (γ : PiecewiseC1Path) (f : ℂ → ℂ),
    IsCompact K → ContinuousOn f γ.trace → Disjoint K γ.trace →
    ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
      ∀ (P : Stieltjes.Partition γ.path.a γ.path.b), Stieltjes.mesh P < δ →
      ∀ tags : Stieltjes.Tags P, ∀ z ∈ K,
        ‖pathSum γ ⟨P, tags⟩ f z - γ.integral (fun w => f w / (w - z))‖ < ε

/-- Finite rational sums approximate the integral uniformly. Q has no zeros
off the cycle, so no possible finite pole is silently allowed elsewhere. -/
def cycle_sums_approximate_type : Prop :=
  ∀ (K : Set ℂ) (Γ : IntegralCycle) (f : ℂ → ℂ),
    IsCompact K → ContinuousOn f Γ.trace → Disjoint K Γ.trace →
    ∀ ε : ℝ, 0 < ε →
      ∃ (s : CycleSampling Γ) (P Q : Polynomial ℂ), Q ≠ 0 ∧
        (∀ z : ℂ, Q.eval z = 0 → z ∈ Γ.trace) ∧
        (∀ z : ℂ, z ∉ Γ.trace → cycleSum Γ s f z = P.eval z / Q.eval z) ∧
        (∀ z ∈ K, ‖cauchyTransform Γ f z - P.eval z / Q.eval z‖ ≤ ε / 2) ∧
        sSup ((fun z => ‖cauchyTransform Γ f z - P.eval z / Q.eval z‖) '' K) < ε

/-- D12.15.03 applied to the preceding polygonal representation. Empty
compact sets, disconnected neighborhoods and arbitrary integer weights are
included. The displayed supremum is the ordinary uniform error on K. -/
def rational_riemann_approximation_type : Prop :=
  ∀ (K U : Set ℂ) (f : ℂ → ℂ),
    IsCompact K → IsOpen U → K ⊆ U → HolomorphicOn U f →
    ∀ ε : ℝ, 0 < ε →
      ∃ (Γ : IntegralCycle) (s : CycleSampling Γ) (P Q : Polynomial ℂ),
        IsPolygonalCycle Γ ∧ Γ.trace ⊆ U \ K ∧ PositivelySeparated K Γ ∧
        (K = ∅ → Γ = 0) ∧ Q ≠ 0 ∧
        (∀ z : ℂ, Q.eval z = 0 → z ∈ Γ.trace) ∧
        (∀ z : ℂ, z ∉ Γ.trace → cycleSum Γ s f z = P.eval z / Q.eval z) ∧
        (∀ z ∈ K, ‖f z - P.eval z / Q.eval z‖ ≤ ε / 2) ∧
        sSup ((fun z => ‖f z - P.eval z / Q.eval z‖) '' K) < ε

end Specs.D12Complex.Ch15.RationalRiemannSums
