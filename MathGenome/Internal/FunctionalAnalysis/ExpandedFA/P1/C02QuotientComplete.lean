import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.P1.C02QuotientComplete
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.P1.C01Banach

/-!
Completeness of the closed distance-norm quotient.

The quotient normed group selected in the specification retains the native
quotient uniform structure. Mathlib's `Submodule.Quotient.completeSpace`
therefore gives completeness of this very structure. The accepted Banach
identification converts it to convergence of every norm Cauchy sequence.
No minimizing representative, linear section, or nontriviality is required.
-/

namespace ExpandedFA.P1.C02QuotientComplete

theorem quotient_complete : Spec.QuotientComplete := by
  intro 𝕜 E _ _ _ M hM hE
  let : IsClosed (M : Set E) := hM
  let : CompleteSpace E := (C01Banach.isBanachSpace_iff_completeSpace E).mp hE
  apply (C01Banach.isBanachSpace_iff_completeSpace (E ⧸ M)).mpr
  exact Submodule.Quotient.completeSpace M

theorem quotient_cauchy_converges : Spec.QuotientCauchyConverges := by
  intro 𝕜 E _ _ _ M hM hE z hz
  obtain ⟨a, ha⟩ := quotient_complete 𝕜 E M hM hE z hz
  obtain ⟨x, rfl⟩ := M.mkQ_surjective a
  exact ⟨x, ha⟩

end ExpandedFA.P1.C02QuotientComplete
