import Mathlib.RingTheory.AdicCompletion.Basic
import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.RingTheory.LocalRing.ResidueField.Defs
import Mathlib.Topology.Algebra.Nonarchimedean.AdicTopology

namespace Specs.CommutativeAlgebraNotes.CoefficientRings

universe u v

/-- A specified residue-field identification for a Cohen ring lifts to a continuous
local map to the complete local ring, with kernel determined by the powers of `p`. -/
def cohenRingMap : Prop :=
  ∀ (R : Type u) [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    [IsAdicComplete (IsLocalRing.maximalIdeal R) R]
    (Λ : Type v) [CommRing Λ] [IsDomain Λ] [IsDiscreteValuationRing Λ]
    [IsAdicComplete (IsLocalRing.maximalIdeal Λ) Λ]
    (p : ℕ) [Fact p.Prime] [CharP (IsLocalRing.ResidueField R) p],
    Ideal.span {(p : Λ)} = IsLocalRing.maximalIdeal Λ →
    ∀ e : (Λ ⧸ Ideal.span {(p : Λ)}) ≃+* IsLocalRing.ResidueField R,
    ∃ φ : Λ →+* R, IsLocalHom φ ∧
      @Continuous Λ R (IsLocalRing.maximalIdeal Λ).adicTopology
        (IsLocalRing.maximalIdeal R).adicTopology φ ∧
      (IsLocalRing.residue R).comp φ =
        e.toRingHom.comp (Ideal.Quotient.mk (Ideal.span {(p : Λ)})) ∧
      (¬ IsNilpotent (p : R) → RingHom.ker φ = ⊥) ∧
      (∀ d : ℕ, 0 < d → (p : R) ^ d = 0 → (∀ n < d, (p : R) ^ n ≠ 0) →
        RingHom.ker φ = Ideal.span {(p : Λ) ^ d})

end Specs.CommutativeAlgebraNotes.CoefficientRings
