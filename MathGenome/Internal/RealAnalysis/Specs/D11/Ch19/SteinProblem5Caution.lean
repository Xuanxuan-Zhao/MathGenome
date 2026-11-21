import MathGenome.Internal.RealAnalysis.Specs.D11.Ch05.NonnegativeIntegral
import Mathlib.Data.PNat.Basic
import Mathlib.Topology.MetricSpace.Bounded
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.MeasureTheory.Function.L1Space.Integrable

/-!
Independent statement of paper.tex:5627–5633. Positive naturals carry the
zero/one metric, not their usual unbounded metric. The real function is
`2^n`, and the atomic Borel measure has weight `2^(-n)` at `n ≥ 1`.
The integral below is the shared supremum over finite simple minorants;
the final clause rules out even a finite-valued assignment realizing all
nonnegative integrals on the literal continuous closed-ball-support class.
-/
open Set MeasureTheory
open scoped ENNReal
noncomputable section
namespace Specs.D11.Ch19.SteinProblem5Caution

structure Space where
  index : ℕ+
  deriving DecidableEq

def positiveIndex : Space ≃ ℕ+ where
  toFun := Space.index
  invFun := Space.mk
  left_inv := fun _ => rfl
  right_inv := fun _ => rfl

instance : Countable Space := positiveIndex.injective.countable
instance : Infinite Space := Infinite.of_injective positiveIndex.symm positiveIndex.symm.injective

instance : MetricSpace Space where
  dist x y := if x = y then 0 else 1
  dist_self x := by simp
  dist_comm x y := by simp [eq_comm]
  dist_triangle x y z := by
    by_cases hxy : x = y <;> by_cases hyz : y = z <;>
      by_cases hxz : x = z <;> simp_all
  eq_of_dist_eq_zero := by intro x y h; by_contra hne; simp [hne] at h

instance : MeasurableSpace Space := borel Space
instance : BorelSpace Space := ⟨rfl⟩

/-- Enumerates exactly the positive integers, beginning with one. -/
def enumeration : ℕ ≃ Space := Equiv.pnatEquivNat.symm.trans positiveIndex.symm

def weight (x : Space) : ℝ≥0∞ := (2 : ℝ≥0∞)⁻¹ ^ (x.index : ℕ)
def testFunction (x : Space) : ℝ := (2 : ℝ) ^ (x.index : ℕ)
def atomicMeasure : Measure Space := Measure.sum (fun k : ℕ =>
  weight (enumeration k) • Measure.dirac (enumeration k))

def counterexample : Prop :=
  (∀ x y : Space, dist x y = if x = y then 0 else 1) ∧
  (∀ g : Space → ℝ, Continuous g) ∧
  (∀ E : Set Space, MeasurableSet E ∧ Bornology.IsBounded E) ∧
  (∀ x : Space, atomicMeasure {x} = weight x) ∧
  atomicMeasure univ = 1 ∧
  (∀ x : Space, ∀ r : ℝ,
    atomicMeasure (Metric.ball x r) < ∞ ∧ atomicMeasure (Metric.closedBall x r) < ∞) ∧
  (∀ x : Space, Metric.closedBall x 1 = univ) ∧
  Continuous testFunction ∧
  (∀ x : Space, 0 ≤ testFunction x) ∧
  (∀ x : Space, tsupport testFunction ⊆ Metric.closedBall x 1) ∧
  Specs.D11.Ch05.NonnegativeIntegral.nonnegativeIntegral_value atomicMeasure
    (fun x => ENNReal.ofReal (testFunction x)) = ∞ ∧
  ¬ Integrable testFunction atomicMeasure ∧
  ¬ ∃ I : (Space → ℝ) → ℝ, ∀ g : Space → ℝ,
    Continuous g → (∃ x : Space, ∃ r : ℝ, tsupport g ⊆ Metric.closedBall x r) →
    (∀ x, 0 ≤ g x) →
    ENNReal.ofReal (I g) = Specs.D11.Ch05.NonnegativeIntegral.nonnegativeIntegral_value atomicMeasure
      (fun x => ENNReal.ofReal (g x))

end Specs.D11.Ch19.SteinProblem5Caution
