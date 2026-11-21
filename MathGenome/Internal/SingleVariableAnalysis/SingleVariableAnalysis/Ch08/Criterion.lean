import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch08.Criterion
import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch08.Integral
import Mathlib.Tactic.Linarith

/-! The Darboux epsilon criterion for bounded real functions.
Approximate the two integral bounds separately, then take a common refinement.
Conversely every partition gap bounds the difference of the integral bounds. -/

namespace SingleVariableAnalysis.Riemann

theorem darboux_criterion : Specs.SingleVariableAnalysis.Ch08.Criterion.darbouxCriterion := by
  intro f a b hab hf
  constructor
  · intro hi ε hε
    have heq : lowerIntegral f hab.le hf = upperIntegral f hab.le hf :=
      (realIntegral_common_value f hi hab.le hf).1.symm.trans
        (realIntegral_common_value f hi hab.le hf).2
    obtain ⟨u, ⟨P, rfl⟩, _hu, hP⟩ :=
      (upperIntegral_isGLB f hab.le hf).exists_between
        (lt_add_of_pos_right _ (half_pos hε))
    obtain ⟨l, ⟨Q, rfl⟩, hQ, _hl⟩ :=
      (lowerIntegral_isLUB f hab.le hf).exists_between
        (sub_lt_self _ (half_pos hε))
    obtain ⟨R, _hpoints, hRP, hRQ⟩ := common_refinement P Q
    refine ⟨R, ?_⟩
    have hu := upper_refinement f P R hf hRP
    have hl := lower_refinement f Q R hf hRQ
    linarith
  · intro hgap
    refine ⟨hab.le, hf, le_antisymm (lowerIntegral_le_upperIntegral f hab.le hf) ?_⟩
    by_contra hnot
    have hpos : 0 < upperIntegral f hab.le hf - lowerIntegral f hab.le hf :=
      sub_pos.mpr (lt_of_not_ge hnot)
    obtain ⟨P, hP⟩ := hgap _ hpos
    have hl := (lowerIntegral_isLUB f hab.le hf).1 ⟨P, rfl⟩
    have hu := (upperIntegral_isGLB f hab.le hf).1 ⟨P, rfl⟩
    linarith

end SingleVariableAnalysis.Riemann
