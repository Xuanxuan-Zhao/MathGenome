import MathGenome.Internal.ProbabilityFoundations.Specs.ProbabilityFoundations.Ch09.IndependentRowObjects
import Mathlib.MeasureTheory.Function.ConvergenceInDistribution
import Mathlib.Probability.Distributions.Gaussian.Real

/-! Independent statement of paper.tex:3126–3151. The row spaces may vary
with n, all row lengths are arbitrary finite numbers, and the tail is strict.
Convergence in distribution here is weak convergence of the pushforward
probability measures, to the real Gaussian of mean zero and variance one. -/

open MeasureTheory ProbabilityTheory Filter Topology

namespace Specs.ProbabilityFoundations.Ch09.LindebergTheorem
open _root_.ProbabilityFoundations.Ch09.IndependentRows
open Specs.ProbabilityFoundations.Ch09.IndependentRows

universe u

def theoremType : Prop :=
  ∀ {r : ℕ → ℕ} {Ω : ℕ → Type u} [∀ n, MeasurableSpace (Ω n)] (R : Row r Ω),
    (∀ n, 0 < varianceSum R n) →
    (∀ ε : ℝ, 0 < ε → Tendsto (fun n => lindeberg R n ε) atTop (𝓝 0)) →
    TendstoInDistribution (sum R) atTop (id : ℝ → ℝ) R.μ (gaussianReal 0 1)

end Specs.ProbabilityFoundations.Ch09.LindebergTheorem
