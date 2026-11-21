import MathGenome.Internal.AlgebraCore.Specs.P103.Ch04.IntegralFiniteGeneration
import Mathlib.RingTheory.IntegralClosure.Algebra.Basic

/-! Theorem 4.5, first two assertions, with the source's unrestricted
commutative ring hypotheses. -/

namespace P103.Ch04.IntegralFiniteGeneration

open Polynomial

theorem integral_iff_monic_equation :
    Specs.integral_iff_monic_equation := by
  intro R A _ _ _ a
  simp only [IsIntegral, RingHom.IsIntegralElem, aeval_def]

/-- Polynomial division by the monic relation reduces every polynomial in `a`
to the indicated finite range of powers. This also holds in the zero algebra. -/
theorem bounded_powers_span :
    Specs.bounded_powers_span := by
  intro R A _ _ _ a p hp ha
  exact Submodule.span_range_natDegree_eq_adjoin hp ha

/-- The library proof inducts over the finite set: the empty set is spanned by
`1`, and adjoining another integral generator multiplies the two finite spans.
The singleton span is given by the bounded powers above. -/
theorem finite_adjoin_of_integral :
    Specs.finite_adjoin_of_integral := by
  intro R A _ _ _ s hs hi
  exact Algebra.finite_adjoin_of_finite_of_isIntegral hs hi

theorem integral_iff_finite_adjoin :
    Specs.integral_iff_finite_adjoin := by
  intro R A _ _ _ a
  constructor
  · intro ha
    exact Algebra.finite_adjoin_simple_of_isIntegral ha
  · intro hfin
    let := hfin
    let a' : Algebra.adjoin R ({a} : Set A) := ⟨a, Algebra.subset_adjoin rfl⟩
    exact (IsIntegral.of_finite R a').map (Algebra.adjoin R ({a} : Set A)).val

theorem finite_iff_integral_and_finiteType :
    Specs.finite_iff_integral_and_finiteType := by
  intro R A _ _ _
  constructor
  · intro hfin
    let := hfin
    exact ⟨fun a => IsIntegral.of_finite R a, inferInstance⟩
  · rintro ⟨hi, ⟨s, hs⟩⟩
    have hfg := fg_adjoin_of_finite s.finite_toSet (fun a _ => hi a)
    exact ⟨by simpa only [hs, Algebra.top_toSubmodule] using hfg⟩

end P103.Ch04.IntegralFiniteGeneration
