import Mathlib.RingTheory.Valuation.ValuationSubring
import Mathlib.RingTheory.LocalRing.LocalSubring

namespace CommutativeAlgebraNotes.ValuationDomination.Specs

universe u v

/-- Every local subring of a field is dominated by a valuation ring with that fraction field. -/
def exists_dominating_valuation_subring : Prop :=
  ∀ (L : Type v) [Field L] (A : LocalSubring L),
    ∃ V : ValuationSubring L, IsFractionRing V L ∧
      ∃ h : A.toSubring ≤ V.toSubring,
        (IsLocalRing.maximalIdeal V).comap (Subring.inclusion h) =
          IsLocalRing.maximalIdeal A.toSubring

/-- A valuation ring of an extension field that dominates the image of a valuation
ring of the base field restricts to that base valuation ring. -/
def comap_eq_of_domination : Prop :=
  ∀ (K : Type u) (L : Type v) [Field K] [Field L]
    (f : K →+* L) (A : ValuationSubring K) (V : ValuationSubring L)
    (h : ∀ a : A, f (a : K) ∈ V),
    (IsLocalRing.maximalIdeal V).comap ((f.comp A.subtype).codRestrict V.toSubring h) =
      IsLocalRing.maximalIdeal A →
    V.comap f = A

end CommutativeAlgebraNotes.ValuationDomination.Specs
