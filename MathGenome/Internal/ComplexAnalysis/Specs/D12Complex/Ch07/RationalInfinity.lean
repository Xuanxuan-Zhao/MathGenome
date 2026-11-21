import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch07.LocalQuotientsArithmetic
import Mathlib.Algebra.Polynomial.Reverse

noncomputable section
open Filter Set
open scoped Topology
namespace Specs.D12Complex.Ch07.RationalInfinity.Objects
open _root_.D12Complex
open Specs.D12Complex.Ch07.LocalQuotientsArithmetic.Objects

/-- The rational expression, whose arbitrary values at denominator zeros are filled below. -/
def rational (P Q : Polynomial ℂ) (z : ℂ) : ℂ := P.eval z / Q.eval z

/-- Fill the rational expression in the finite and reciprocal source coordinates. -/
def extension (P Q : Polynomial ℂ) : RiemannSphere → RiemannSphere :=
  fun p => OnePoint.elim p (fill (reciprocalPullback (rational P Q)) 0)
    (fill (rational P Q))

/-- A zero of exact positive order in the reciprocal coordinate, with a holomorphic unit. -/
def ZeroOfOrderAtInfinity (f : ℂ → ℂ) (m : ℕ) : Prop :=
  1 ≤ m ∧ IsolatedSingularityAtInfinity f ∧
    ∃ r : ℝ, 0 < r ∧ ∃ g : ℂ → ℂ, HolomorphicOn (Metric.ball 0 r) g ∧
      g 0 ≠ 0 ∧ ∀ w ∈ puncturedDisk 0 r, f w⁻¹ = w ^ m * g w
end Specs.D12Complex.Ch07.RationalInfinity.Objects

namespace Specs.D12Complex.Ch07.RationalInfinity
open _root_.D12Complex
open Objects

def rational_type := Polynomial ℂ → Polynomial ℂ → ℂ → ℂ
def rational_value : rational_type := fun P Q z => P.eval z / Q.eval z

def extension_type := Polynomial ℂ → Polynomial ℂ → RiemannSphere → RiemannSphere
def extension_value : extension_type := fun P Q p => OnePoint.elim p
  (LocalQuotientsArithmetic.Objects.fill (reciprocalPullback (rational P Q)) 0)
  (LocalQuotientsArithmetic.Objects.fill (rational P Q))

def ZeroOfOrderAtInfinity_type := (ℂ → ℂ) → ℕ → Prop
def ZeroOfOrderAtInfinity_value : ZeroOfOrderAtInfinity_type := fun f m =>
  1 ≤ m ∧ IsolatedSingularityAtInfinity f ∧
    ∃ r : ℝ, 0 < r ∧ ∃ g : ℂ → ℂ, HolomorphicOn (Metric.ball 0 r) g ∧
      g 0 ≠ 0 ∧ ∀ w ∈ puncturedDisk 0 r, f w⁻¹ = w ^ m * g w

def meromorphic_extension_type : Prop := ∀ (P Q : Polynomial ℂ), Q ≠ 0 →
  ScalarMeromorphicOnSphere univ (extension P Q) ∧
    ∀ z : ℂ, Q.eval z ≠ 0 → extension P Q (sphereFinite z) =
      sphereFinite (P.eval z / Q.eval z)

def order_at_infinity_type : Prop := ∀ (P Q : Polynomial ℂ), P ≠ 0 → Q ≠ 0 →
  IsRelPrime P Q →
  meromorphicOrderAt (reciprocalPullback (rational P Q)) 0 =
    ((Q.natDegree : ℤ) - (P.natDegree : ℤ) : WithTop ℤ)

def sphere_order_at_infinity_type : Prop := ∀ (P Q : Polynomial ℂ), P ≠ 0 → Q ≠ 0 →
  IsRelPrime P Q → sphereScalarSignedOrder (extension P Q) sphereInfty =
    some ((Q.natDegree : ℤ) - (P.natDegree : ℤ))

def infinity_values_type : Prop := ∀ (P Q : Polynomial ℂ), P ≠ 0 → Q ≠ 0 →
  IsRelPrime P Q →
    (Q.natDegree < P.natDegree → extension P Q sphereInfty = sphereInfty) ∧
    (P.natDegree < Q.natDegree → extension P Q sphereInfty = sphereFinite 0)

def pole_at_infinity_type : Prop := ∀ (P Q : Polynomial ℂ), P ≠ 0 → Q ≠ 0 →
  IsRelPrime P Q → Q.natDegree < P.natDegree →
    PoleOfOrderAtInfinity (rational P Q) (P.natDegree - Q.natDegree)

def zero_at_infinity_type : Prop := ∀ (P Q : Polynomial ℂ), P ≠ 0 → Q ≠ 0 →
  IsRelPrime P Q → P.natDegree < Q.natDegree →
    ZeroOfOrderAtInfinity (rational P Q) (Q.natDegree - P.natDegree)

def value_at_infinity_type : Prop := ∀ (P Q : Polynomial ℂ), P ≠ 0 → Q ≠ 0 →
  IsRelPrime P Q → P.natDegree = Q.natDegree →
    RemovableSingularityAtInfinity (rational P Q) ∧
    Tendsto (reciprocalPullback (rational P Q)) (𝓝[≠] 0)
      (𝓝 (P.leadingCoeff / Q.leadingCoeff)) ∧
    extension P Q sphereInfty = sphereFinite (P.leadingCoeff / Q.leadingCoeff) ∧
    P.leadingCoeff / Q.leadingCoeff ≠ 0

def zero_rational_type : Prop := ∀ (Q : Polynomial ℂ), Q ≠ 0 →
  extension 0 Q = (fun _ => sphereFinite 0) ∧
    ScalarMeromorphicOnSphere univ (extension 0 Q) ∧
    RemovableSingularityAtInfinity (rational 0 Q)
end Specs.D12Complex.Ch07.RationalInfinity
