import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.P1.C01RieszLemma
import Mathlib.Analysis.Normed.Module.RieszLemma

/-! Riesz's lemma with a strict bound on the infimum distance. -/

namespace ExpandedFA.P1.C01RieszLemma

/-- Riesz's lemma for proper closed subspaces over either manuscript scalar
field, with no completeness or dimension assumption. -/
theorem riesz_lemma : Spec.RieszLemma := by
  intro 𝕜 E _ _ _ M hM hclosed θ _hθpos hθone
  have hproper : ∃ y : E, y ∉ M := by
    by_contra! h
    exact hM (top_unique (fun y _ => h y))
  -- Use a strictly larger parameter before passing to the infimum: a
  -- pointwise strict bound at θ alone would not imply a strict infimum bound.
  obtain ⟨r, hθr, hrone⟩ := exists_between hθone
  obtain ⟨x, _hxM, hxnorm, hx⟩ :=
    _root_.riesz_lemma_of_lt_one hclosed hproper hrone
  refine ⟨x, hxnorm, hθr.trans_le ?_⟩
  apply (Metric.le_infDist (show (M : Set E).Nonempty from ⟨0, M.zero_mem⟩)).2
  intro m hm
  simpa only [dist_eq_norm] using hx m hm

end ExpandedFA.P1.C01RieszLemma
