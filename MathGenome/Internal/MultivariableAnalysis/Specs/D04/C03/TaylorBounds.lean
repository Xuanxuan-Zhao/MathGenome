import MathGenome.Internal.MultivariableAnalysis.Specs.D04.C03.HigherInterfaces
import MathGenome.Internal.MultivariableAnalysis.Specs.D04.C02.SegmentMeanValue
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-! Independent statements for the full remainder-bounds corollary and the
vector Lagrange obstruction. Scalar targets are ℝ; vector targets use E m.
The coordinate hypothesis concerns every ordered partial of the stated order. -/
noncomputable section
open Set
open scoped BigOperators
namespace Specs.D04.C03.TaylorBounds
open Specs.D04.C01.EuclideanInterfaces.Model
open Specs.D04.C02.DerivativeInterfaces.Model
open Specs.D04.C03.HigherInterfaces.Model

def taylor_remainder_boundType : Prop :=
  ∀ {n m : ℕ} (k : ℕ) (U : Set (E n)) (f : E n → E m) (a h : E n) (M : ℝ),
    IsOpen U → CrOn (k+1) U f →
    (∀ t ∈ Icc (0 : ℝ) 1, a + t • h ∈ U) →
    (∀ t ∈ Icc (0 : ℝ) 1, ‖higherDifferential (k+1) f (a+t•h)‖ ≤ M) →
    ‖taylorRemainder k f a h‖ ≤ M * ‖h‖^(k+1) / ((k+1).factorial : ℝ)

def scalar_taylor_lagrangeType : Prop :=
  ∀ {n : ℕ} (k : ℕ) (U : Set (E n)) (f : E n → ℝ) (a h : E n),
    IsOpen U → CrOn (k+1) U f →
    (∀ t ∈ Icc (0 : ℝ) 1, a + t • h ∈ U) → h ≠ 0 →
    ∃ t ∈ Ioo (0 : ℝ) 1, taylorRemainder k f a h =
      differentialDiagonal (higherDifferential (k+1) f (a+t•h)) h /
        ((k+1).factorial : ℝ)

def scalar_taylor_coordinate_boundsType : Prop :=
  ∀ {n : ℕ} (k : ℕ) (U : Set (E n)) (f : E n → ℝ) (a h : E n) (C : ℝ),
    IsOpen U → CrOn (k+1) U f →
    (∀ t ∈ Icc (0 : ℝ) 1, a + t • h ∈ U) →
    (∀ t ∈ Icc (0 : ℝ) 1, ∀ j : Fin (k+1) → Fin n,
      |orderedPartial (List.ofFn j) f (a+t•h)| ≤ C) →
    |taylorRemainder k f a h| ≤ C * (∑ i : Fin n, |h i|)^(k+1) / ((k+1).factorial : ℝ) ∧
    C * (∑ i : Fin n, |h i|)^(k+1) / ((k+1).factorial : ℝ) ≤
      C * (n : ℝ)^((k+1 : ℝ)/2) * ‖h‖^(k+1) / ((k+1).factorial : ℝ)

def taylor_bounds_dimension_zeroType : Prop :=
  ∀ {m : ℕ} (k : ℕ) (f : E 0 → E m) (a h : E 0),
    h = 0 ∧ taylorRemainder k f a h = 0

/-- An exact vector Lagrange rule for all degrees includes the false degree-zero
rule for the paper's polynomial curve. This states the failure on that curve
using the actual Taylor remainder and higher differential. -/
def vector_taylor_lagrange_failureType : Prop :=
  CrOn 1 (Set.univ : Set ℝ) Specs.D04.C02.SegmentMeanValue.Model.meanValueCounterexample ∧
  ¬ ∃ t ∈ Ioo (0 : ℝ) 1,
    taylorRemainder 0 Specs.D04.C02.SegmentMeanValue.Model.meanValueCounterexample 0 1 =
      differentialDiagonal (higherDifferential 1
        Specs.D04.C02.SegmentMeanValue.Model.meanValueCounterexample t) (1 : ℝ)

end Specs.D04.C03.TaylorBounds
