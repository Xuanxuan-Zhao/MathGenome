import Mathlib.Algebra.CharP.Defs
import Mathlib.RingTheory.AdicCompletion.Basic
import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.RingTheory.LocalRing.ResidueField.Defs
import Mathlib.Topology.Algebra.Nonarchimedean.AdicTopology

namespace Specs.CommutativeAlgebraNotes.CoefficientRings

open IsLocalRing

universe u

/-- A complete Noetherian local ring has a coefficient field in equal characteristic
and a Cohen coefficient map in positive residue characteristic. -/
def completeLocalCoefficientRings : Prop :=
  ∀ (R : Type u) [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    [IsAdicComplete (maximalIdeal R) R],
    (ringChar (ResidueField R) = ringChar R →
      ∃ σ : ResidueField R →+* R,
        (residue R).comp σ = RingHom.id (ResidueField R) ∧ Function.Injective σ) ∧
    (∀ (p : ℕ), p.Prime → ∀ [CharP (ResidueField R) p],
      ∃ (Λ : Type u) (_ : CommRing Λ) (_ : IsDomain Λ) (_ : IsDiscreteValuationRing Λ),
        CharZero Λ ∧ IsAdicComplete (maximalIdeal Λ) Λ ∧
        maximalIdeal Λ = Ideal.span {(p : Λ)} ∧
        ∃ (e : ResidueField Λ ≃+* ResidueField R) (φ : Λ →+* R),
          IsLocalHom φ ∧
          @Continuous Λ R (maximalIdeal Λ).adicTopology (maximalIdeal R).adicTopology φ ∧
          (residue R).comp φ = e.toRingHom.comp (residue Λ) ∧
          (¬ IsNilpotent (p : R) → RingHom.ker φ = ⊥) ∧
          (∀ d : ℕ, 0 < d → (p : R) ^ d = 0 →
            (∀ n < d, (p : R) ^ n ≠ 0) → RingHom.ker φ = Ideal.span {(p : Λ) ^ d}))

end Specs.CommutativeAlgebraNotes.CoefficientRings
