import MathGenome.Internal.ProbabilityFoundations.Specs.ProbabilityFoundations.Ch09.IndependentRowObjects
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.Probability.Distributions.Gaussian.Real

/-! The Feller converse, paper.tex:3117–3124 and 3156–3183.
Each row has its own probability space, with no cross-row independence.
The sum is tested in the canonical weak topology on Borel probability measures.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Filter Topology
open scoped BigOperators

namespace Specs.ProbabilityFoundations.Ch09.FellerConverse
open _root_.ProbabilityFoundations.Ch09.IndependentRows
open Specs.ProbabilityFoundations.Ch09.IndependentRows

universe u

/-- Full converse under positive total row variance and vanishing maximal
normalized variance. All thresholds are strictly positive and the tails strict. -/
def conclusion : Prop :=
  ∀ {r : ℕ → ℕ} {Ω : ℕ → Type u} [∀ n, MeasurableSpace (Ω n)]
    (R : Row r Ω),
    (∀ n, 0 < varianceSum R n) →
    Tendsto (β := ProbabilityMeasure ℝ) (fun n => (⟨(R.μ n).map (sum R n),
      inferInstance⟩ :
      ProbabilityMeasure ℝ)) atTop (𝓝 (⟨gaussianReal 0 1, inferInstance⟩ : ProbabilityMeasure ℝ)) →
    Tendsto (maxVariance R) atTop (𝓝 0) →
    ∀ ε : ℝ, 0 < ε → Tendsto (fun n => lindeberg R n ε) atTop (𝓝 0)

end Specs.ProbabilityFoundations.Ch09.FellerConverse
