import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.InfimalConvolution.ReflexiveFullConeDuality
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.InfimalConvolution.ReflexiveExactness

namespace ExpandedFA.InfimalConvolution.ReflexiveFullConeDuality

universe u

open ExpandedFA.P1 ExtendedConvexFunctions C06Conjugates
open Definitions DomainConjugateIdentities

/-- The full-cone estimate includes empty bounded sets. -/
theorem uniform_split_bounds : Spec.UniformSplitBounds.{u} :=
  UniformSplitBounds.uniform_split_bounds

theorem norm_lowerSemicontinuity : Spec.NormLowerSemicontinuity.{u} :=
  ReflexiveExactness.norm_lowerSemicontinuity

/-- Equality of infima holds also at infinite values. -/
theorem exact_conjugate_formula : Spec.ExactConjugateFormula.{u} :=
  ReflexiveExactness.exact_conjugate_formula

theorem finite_attainment : Spec.FiniteAttainment.{u} :=
  ReflexiveExactness.finite_attainment

theorem exact_domain_sum : Spec.ExactDomainSum.{u} :=
  ReflexiveExactness.exact_domain_sum

/-- Negation interchanges arbitrary extended-real infima and suprema. -/
lemma neg_iInf_eq_iSup {ι : Sort*} (F : ι → EReal) :
    -(⨅ i, F i) = ⨆ i, -F i := by
  apply le_antisymm
  · apply EReal.neg_le.mpr
    apply le_iInf
    intro i
    exact EReal.neg_le.mpr (le_iSup (fun j => -F j) i)
  · apply iSup_le
    intro i
    exact EReal.le_neg.mpr (by simpa only [neg_neg] using iInf_le F i)

/-- At zero the conjugate is the negative of the primal infimum. -/
lemma conjugate_zero (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]
    (Φ : ExtendedFunction E) :
    convexConjugate E Φ 0 = -(⨅ x, extendedRealValue (Φ x)) := by
  rw [neg_iInf_eq_iSup]
  unfold convexConjugate
  simp

/-- Properness of the two inputs makes negation of their cost legitimate,
even when one or both conjugates equal +∞. -/
lemma negative_zero_cost (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]
    (φ ψ : ExtendedFunction E)
    (hp : ExtendedConvexFunctions.Spec.ProperValue E φ)
    (hq : ExtendedConvexFunctions.Spec.ProperValue E ψ) (g : E →L[ℝ] ℝ) :
    -conjugateSplitCost E φ ψ 0 g =
      -convexConjugate E φ (-g) - convexConjugate E ψ g := by
  unfold conjugateSplitCost
  rw [zero_sub]
  exact EReal.neg_add (.inl (convexConjugate_ne_bot E φ hp (-g)))
    (.inr (convexConjugate_ne_bot E ψ hq g))

theorem primal_dual_identity : Spec.PrimalDualIdentity := by
  intro E _ _ _ href φ ψ hp hq hcommon hcone
  change (⨅ x, extendedRealValue (φ x + ψ x)) =
    ⨆ g : E →L[ℝ] ℝ, -convexConjugate E φ (-g) - convexConjugate E ψ g
  have heq := exact_conjugate_formula E href φ ψ hp hq hcommon hcone 0
  change infimalConvolution E φ ψ 0 = convexConjugate E (fun x => φ x + ψ x) 0 at heq
  have hneg := congrArg Neg.neg heq
  rw [conjugate_zero, neg_neg] at hneg
  rw [← hneg]
  unfold infimalConvolution
  rw [neg_iInf_eq_iSup]
  simp_rw [negative_zero_cost E φ ψ hp.1 hq.1]

theorem dual_attainment : Spec.DualAttainment := by
  intro E _ _ _ href φ ψ hp hq hcommon hcone r hr
  change (⨅ x, extendedRealValue (φ x + ψ x)) = (r : EReal) at hr
  have hz : convexConjugate E (fun x => φ x + ψ x) 0 = ((-r : ℝ) : EReal) := by
    rw [conjugate_zero, hr, EReal.coe_neg]
  obtain ⟨g, hg⟩ := finite_attainment E href φ ψ hp hq hcommon hcone 0 (-r) hz
  change conjugateSplitCost E φ ψ 0 g = ((-r : ℝ) : EReal) at hg
  have hvalue : -convexConjugate E φ (-g) - convexConjugate E ψ g = (r : EReal) := by
    rw [← negative_zero_cost E φ ψ hp.1 hq.1 g, hg, EReal.coe_neg, neg_neg]
  refine ⟨g, hvalue, ?_⟩
  intro u
  change -convexConjugate E φ (-u) - convexConjugate E ψ u ≤
    -convexConjugate E φ (-g) - convexConjugate E ψ g
  have hdual := primal_dual_identity E href φ ψ hp hq hcommon hcone
  change (⨅ x, extendedRealValue (φ x + ψ x)) =
    (⨆ v : E →L[ℝ] ℝ, -convexConjugate E φ (-v) - convexConjugate E ψ v) at hdual
  calc
    _ ≤ ⨆ v : E →L[ℝ] ℝ, -convexConjugate E φ (-v) - convexConjugate E ψ v :=
      le_iSup (fun v : E →L[ℝ] ℝ =>
        -convexConjugate E φ (-v) - convexConjugate E ψ v) u
    _ = (r : EReal) := hdual.symm.trans hr
    _ = _ := hvalue.symm

theorem primal_not_top : Spec.PrimalNotTop := by
  intro E φ ψ hcommon
  obtain ⟨x, hx, hy⟩ := hcommon
  change φ x ≠ ⊤ at hx
  change ψ x ≠ ⊤ at hy
  obtain ⟨r, hr⟩ := WithTop.ne_top_iff_exists.mp hx
  obtain ⟨s, hs⟩ := WithTop.ne_top_iff_exists.mp hy
  change (⨅ x, extendedRealValue (φ x + ψ x)) ≠ ⊤
  apply ne_top_of_le_ne_top _ (iInf_le (fun x => extendedRealValue (φ x + ψ x)) x)
  rw [← hr, ← hs, ← WithTop.coe_add]
  exact EReal.coe_ne_top (r + s)

theorem unbounded_below_duality : Spec.UnboundedBelowDuality := by
  intro E _ _ _ href φ ψ hp hq hcommon hcone hbot
  rw [← primal_dual_identity E href φ ψ hp hq hcommon hcone]
  exact hbot

end ExpandedFA.InfimalConvolution.ReflexiveFullConeDuality
