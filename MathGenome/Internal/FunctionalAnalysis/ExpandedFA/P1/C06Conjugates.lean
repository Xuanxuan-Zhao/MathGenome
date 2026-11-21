import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.P1.C06Conjugates
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.P1.ExtendedConvexFunctions
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.P1.C04Dual

/-! Conjugation with the continuous real-linear dual, without any completeness
assumption. The definitions also make sense for nonproper inputs; on the
manuscript's proper inputs the conjugate never equals −∞. -/
namespace ExpandedFA.P1.C06Conjugates

open ExtendedConvexFunctions

/-- The canonical order-preserving inclusion `(-∞,+∞] → [-∞,+∞]`. -/
def extendedRealValue : Spec.ExtendedRealValueType := WithBot.some

/-- φ*(f) = sup_x (f(x) − φ(x)). In particular an input value +∞ contributes −∞. -/
noncomputable def convexConjugate (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]
    (φ : ExtendedFunction E) (f : C04Dual.ContinuousDual ℝ E) : EReal :=
  ⨆ x, (f x : EReal) - extendedRealValue (φ x)

/-- φ**(x) = sup_f (f(x) − φ*(f)), with the same continuous real-linear dual.
A conjugate value +∞ contributes −∞. -/
noncomputable def convexBiconjugate (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]
    (φ : ExtendedFunction E) (x : E) : EReal :=
  ⨆ f : C04Dual.ContinuousDual ℝ E, (f x : EReal) - convexConjugate E φ f

theorem extendedRealValue_conventions : Spec.ExtendedRealValueConventions := by
  refine ⟨fun _ => rfl, rfl, ?_, ?_⟩
  · intro a
    exact WithBot.coe_ne_bot
  · intro a b
    exact WithBot.coe_le_coe

theorem conjugate_subtraction_conventions : Spec.SubtractionConventions := by
  refine ⟨?_, ?_, ?_⟩
  · intro r s
    exact (EReal.coe_sub r s).symm
  · intro r
    exact EReal.sub_top (r : EReal)
  · intro r
    exact EReal.sub_top (r : EReal)

theorem convexConjugate_ne_bot : Spec.ConjugateNeverBottom := by
  intro E _ _ φ hφ f
  obtain ⟨x, r, hr⟩ := (proper_iff_finite_value E φ).mp hφ
  have hle : ((f x - r : ℝ) : EReal) ≤ convexConjugate E φ f := by
    calc
      ((f x - r : ℝ) : EReal) = (f x : EReal) - extendedRealValue (φ x) := by
        rw [hr]
        rfl
      _ ≤ convexConjugate E φ f := by
        unfold convexConjugate
        exact le_iSup (fun y : E => (f y : EReal) - extendedRealValue (φ y)) x
  exact ne_bot_of_le_ne_bot (EReal.coe_ne_bot _) hle

theorem convexConjugate_isLUB : Spec.ConjugateIsLUB := by
  intro E _ _ φ f
  exact isLUB_iSup

theorem convexBiconjugate_isLUB : Spec.BiconjugateIsLUB := by
  intro E _ _ φ x
  exact isLUB_iSup

end ExpandedFA.P1.C06Conjugates
