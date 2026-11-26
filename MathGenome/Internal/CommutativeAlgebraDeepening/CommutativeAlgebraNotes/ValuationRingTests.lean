import Mathlib.RingTheory.Valuation.ValuationRing

universe u v

namespace CommutativeAlgebraNotes

/-- The fraction-field, ideal-order, and local-principality tests for valuation rings. -/
theorem intrinsicValuationTests (V : Type u) (K : Type v) [CommRing V] [IsDomain V]
    [Field K] [Algebra V K] [IsFractionRing V K] :
    (ValuationRing V ↔ ∀ x : K, x ≠ 0 →
      x ∈ (algebraMap V K).range ∨ x⁻¹ ∈ (algebraMap V K).range) ∧
    (ValuationRing V ↔ ∀ I J : Ideal V, I ≤ J ∨ J ≤ I) ∧
    (ValuationRing V ↔ IsLocalRing V ∧ ∀ I : Ideal V, I.FG → I.IsPrincipal) := by
  refine ⟨?_, ?_, ?_⟩
  · constructor
    · intro h x _
      exact (ValuationRing.iff_isInteger_or_isInteger V K).mp h x
    · intro h
      apply (ValuationRing.iff_isInteger_or_isInteger V K).mpr
      intro x
      by_cases hx : x = 0
      · subst x
        exact Or.inl IsLocalization.isInteger_zero
      · exact h x hx
  · exact ValuationRing.iff_ideal_total.trans ⟨fun h => h.total, fun h => ⟨h⟩⟩
  · exact ValuationRing.iff_local_bezout_domain.trans
      ⟨fun ⟨hLocal, hBezout⟩ => ⟨hLocal, hBezout.isPrincipal_of_FG⟩,
        fun ⟨hLocal, hPrincipal⟩ => ⟨hLocal, ⟨hPrincipal⟩⟩⟩

end CommutativeAlgebraNotes
