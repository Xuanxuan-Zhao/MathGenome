import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
import Mathlib.RingTheory.Valuation.ValuationSubring

namespace Specs.CommutativeAlgebraNotes

universe u

/-- Theorem 5.17 as an equality of subrings of the ambient field. -/
def integralClosure_eq_iInf_valuationSubring : Prop :=
  ∀ {L : Type u} [Field L] (A : Subring L),
    (integralClosure A L).toSubring =
      ⨅ V : {V : ValuationSubring L // A ≤ V.toSubring}, V.val.toSubring

/-- The same valuative criterion expressed as an elementwise equivalence. -/
def isIntegral_iff_forall_valuationSubring : Prop :=
  ∀ {L : Type u} [Field L] (A : Subring L) (x : L),
    IsIntegral A x ↔ ∀ V : ValuationSubring L, A ≤ V.toSubring → x ∈ V.toSubring

end Specs.CommutativeAlgebraNotes
