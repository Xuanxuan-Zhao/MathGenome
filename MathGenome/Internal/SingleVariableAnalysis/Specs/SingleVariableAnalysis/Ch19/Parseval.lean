import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch19.FiniteProjection
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Analysis.Real.Sqrt

/-! K03.19.parseval, paper.tex:4992–5011. Coefficients and all energies use
proper Darboux integrals on [-π,π]. The existential witnesses assert their
existence from continuity and periodicity; they add no hypotheses. The square
root of the normalized energy is the manuscript's L² seminorm on actual
functions. The real statement uses the canonical embedding into ℂ. -/
noncomputable section
namespace Specs.SingleVariableAnalysis.Ch19.Parseval
open Ch08.Integral PeriodicSetup Representation FiniteProjection
open scoped BigOperators

def complexParseval : Prop := ∀ (f : ℝ → ℂ), Continuous f →
  Function.Periodic f (2 * Real.pi) →
  ∃ (h : ComplexWeights f)
    (hs : realIntegrableValue (fun x => ‖f x‖ ^ 2) (-Real.pi) Real.pi)
    (hr : ∀ N : ℕ, realIntegrableValue
      (fun x => ‖f x - partialSumValue f h N x‖ ^ 2) (-Real.pi) Real.pi),
    Summable (fun n : ℤ => ‖coefficientValue f n (h n)‖ ^ 2) ∧
    (∑' n : ℤ, ‖coefficientValue f n (h n)‖ ^ 2) = normSquaredValue f hs ∧
    Filter.Tendsto (fun N => normSquaredValue
      (fun x => f x - partialSumValue f h N x) (hr N)) Filter.atTop (nhds 0) ∧
    Filter.Tendsto (fun N => Real.sqrt (normSquaredValue
      (fun x => f x - partialSumValue f h N x) (hr N))) Filter.atTop (nhds 0) ∧
    Filter.Tendsto (fun N : ℕ => ∑ n ∈ Finset.Icc (-(N : ℤ)) (N : ℤ),
      ‖coefficientValue f n (h n)‖ ^ 2) Filter.atTop (nhds (normSquaredValue f hs))

def realParseval : Prop := ∀ (f : ℝ → ℝ), Continuous f →
  Function.Periodic f (2 * Real.pi) →
  ∃ (h : ComplexWeights (fun x => (f x : ℂ)))
    (hs : realIntegrableValue (fun x => |f x| ^ 2) (-Real.pi) Real.pi)
    (hr : ∀ N : ℕ, realIntegrableValue
      (fun x => ‖(f x : ℂ) - partialSumValue (fun y => (f y : ℂ)) h N x‖ ^ 2)
        (-Real.pi) Real.pi),
    Summable (fun n : ℤ => ‖coefficientValue (fun x => (f x : ℂ)) n (h n)‖ ^ 2) ∧
    (∑' n : ℤ, ‖coefficientValue (fun x => (f x : ℂ)) n (h n)‖ ^ 2) =
      (1 / (2 * Real.pi)) * realIntegralValue (fun x => |f x| ^ 2) hs ∧
    Filter.Tendsto (fun N => normSquaredValue
      (fun x => (f x : ℂ) - partialSumValue (fun y => (f y : ℂ)) h N x) (hr N))
      Filter.atTop (nhds 0) ∧
    Filter.Tendsto (fun N => Real.sqrt (normSquaredValue
      (fun x => (f x : ℂ) - partialSumValue (fun y => (f y : ℂ)) h N x) (hr N)))
      Filter.atTop (nhds 0)

end Specs.SingleVariableAnalysis.Ch19.Parseval
