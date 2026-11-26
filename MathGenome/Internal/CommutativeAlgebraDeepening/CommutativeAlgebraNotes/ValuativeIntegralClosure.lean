import Mathlib.RingTheory.Valuation.LocalSubring

namespace CommutativeAlgebraNotes

universe u

variable {L : Type u} [Field L]

/-- Theorem 5.17. The integral closure in a field is the intersection of the
valuation subrings containing the given subring. -/
theorem integralClosure_eq_iInf_valuationSubring (A : Subring L) :
    (integralClosure A L).toSubring =
      ⨅ V : {V : ValuationSubring L // A ≤ V.toSubring}, V.val.toSubring := by
  calc
    (integralClosure A L).toSubring =
        (integralClosure (Subring.closure (A : Set L)) L).toSubring :=
      congrArg (fun B : Subring L => (integralClosure B L).toSubring)
        (Subring.closure_eq A).symm
    _ = _ := (iInf_valuationSubring_superset (s := (A : Set L))).symm

/-- An element of the ambient field is integral exactly when it belongs to
every valuation subring containing the base subring. -/
theorem isIntegral_iff_forall_valuationSubring (A : Subring L) (x : L) :
    IsIntegral A x ↔ ∀ V : ValuationSubring L, A ≤ V.toSubring → x ∈ V.toSubring := by
  change x ∈ (integralClosure A L).toSubring ↔ _
  rw [integralClosure_eq_iInf_valuationSubring, Subring.mem_iInf]
  exact ⟨fun h V hV => h ⟨V, hV⟩, fun h V => h V.val V.property⟩

end CommutativeAlgebraNotes
