import Mathlib.RingTheory.AdicCompletion.Topology
import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.RingTheory.MvPowerSeries.Inverse
import Mathlib.RingTheory.RegularLocalRing.Defs

namespace CommutativeAlgebraNotes.CoefficientRings.Specs

open IsLocalRing

universe u

/-- The unramified mixed-characteristic case of the complete regular local
presentation theorem. The residue field of the series ring is identified with
that of the coefficient DVR by taking the residue of the constant coefficient. -/
def unramifiedRegularPresentationType : Prop :=
  ∀ (R : Type u) [CommRing R] [IsRegularLocalRing R] [CharZero R]
    [IsAdicComplete (maximalIdeal R) R]
    (p d : ℕ) (_ : p.Prime) [CharP (ResidueField R) p],
    ringKrullDim R = (d : WithBot ℕ∞) →
    (p : R) ∉ maximalIdeal R ^ 2 →
    0 < d ∧
      ∃ (Λ : Type u) (_ : CommRing Λ) (_ : IsDomain Λ) (_ : IsDiscreteValuationRing Λ),
        CharZero Λ ∧ IsAdicComplete (maximalIdeal Λ) Λ ∧
        maximalIdeal Λ = Ideal.span {(p : Λ)} ∧
        ∃ (e : ResidueField Λ ≃+* ResidueField R) (φ : Λ →+* R),
          IsLocalHom φ ∧
          @Continuous Λ R (maximalIdeal Λ).adicTopology (maximalIdeal R).adicTopology φ ∧
          (∀ a, residue R (φ a) = e (residue Λ a)) ∧
          ∃ E : MvPowerSeries (Fin (d - 1)) Λ ≃+* R,
            (∀ a, E (MvPowerSeries.C a) = φ a) ∧
            ∀ f, residue R (E f) = e (residue Λ (MvPowerSeries.constantCoeff f))

end CommutativeAlgebraNotes.CoefficientRings.Specs
