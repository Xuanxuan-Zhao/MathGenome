import Mathlib.RingTheory.AdicCompletion.Basic
import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.RingTheory.LocalRing.ResidueField.Basic

namespace CommutativeAlgebraNotes.CoefficientRings.Specs

universe u

open IsLocalRing

/-- A field of characteristic `p` is the residue field of a complete DVR
of characteristic zero with uniformizer the image of the rational prime `p`. -/
def cohenRingExistenceType : Prop :=
  ∀ (p : ℕ) (_ : p.Prime) (k : Type u) [Field k] [CharP k p],
    ∃ (Λ : Type u) (_ : CommRing Λ) (_ : IsDomain Λ) (_ : IsDiscreteValuationRing Λ),
      CharZero Λ ∧ IsAdicComplete (maximalIdeal Λ) Λ ∧
        maximalIdeal Λ = Ideal.span {(p : Λ)} ∧ Nonempty (ResidueField Λ ≃+* k)

end CommutativeAlgebraNotes.CoefficientRings.Specs
