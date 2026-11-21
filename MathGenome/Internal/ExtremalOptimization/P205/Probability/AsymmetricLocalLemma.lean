import MathGenome.Internal.ExtremalOptimization.P205.Probability.LocalLemmaConditionals
import MathGenome.Internal.ExtremalOptimization.Specs.P205.Probability.AsymmetricLocalLemma

open MeasureTheory
open scoped BigOperators Classical

universe u v

namespace P205.Probability

/-- Finite asymmetric Lovász local lemma, including the quantitative product
lower bound and its strict positivity (Theorem 6.2, p205:W28). -/
theorem asymmetricLocalLemma : Specs.P205.Probability.AsymmetricLocalLemmaType.{u, v} := by
  intro I _ Ω _ μ _ A D x hD hx hprob
  have hbound := avoidance_extension_lower μ A hD.1 x (fun i => (hx i).2.le)
    Finset.univ
    (fun R _ i hi => (localLemmaConditionals_mul μ A D x hD hx hprob R).2 i hi)
    ∅ Finset.univ (by simp) (by simp)
  refine ⟨?_, Finset.prod_pos (fun i _ => sub_pos.mpr (hx i).2)⟩
  simpa [avoidEvents] using hbound

end P205.Probability
