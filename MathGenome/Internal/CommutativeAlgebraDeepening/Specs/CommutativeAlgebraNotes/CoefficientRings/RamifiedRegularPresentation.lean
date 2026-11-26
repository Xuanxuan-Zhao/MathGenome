import Mathlib.RingTheory.AdicCompletion.Basic
import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.RingTheory.LocalRing.ResidueField.Basic
import Mathlib.RingTheory.MvPowerSeries.Inverse
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.Topology.Algebra.Nonarchimedean.AdicTopology

namespace Specs.CommutativeAlgebraNotes.CoefficientRings

open IsLocalRing
open scoped nonZeroDivisors

universe u

/-- A complete ramified regular local ring is cut out in an unramified
power series ring by one equation with linear term the uniformizer. -/
def RamifiedRegularPresentation : Prop :=
  ∀ (R : Type u) [CommRing R] [IsRegularLocalRing R] [CharZero R]
    [IsAdicComplete (maximalIdeal R) R]
    (p d : ℕ) [Fact p.Prime] [CharP (ResidueField R) p],
    ringKrullDim R = (d : WithBot ℕ∞) →
    (p : R) ∈ maximalIdeal R ^ 2 →
    ∃ (V : Type u) (_ : CommRing V) (_ : IsDomain V) (_ : IsDiscreteValuationRing V),
      CharZero V ∧ IsAdicComplete (maximalIdeal V) V ∧
      maximalIdeal V = Ideal.span {(p : V)} ∧
      ∃ (e : ResidueField V ≃+* ResidueField R) (φ : V →+* R),
        IsLocalHom φ ∧ Function.Injective φ ∧
        (residue R).comp φ = e.toRingHom.comp (residue V) ∧
        ∃ x : Fin d → R, Ideal.span (Set.range x) = maximalIdeal R ∧
          let S := MvPowerSeries (Fin d) V
          let J := Ideal.span (Set.range (MvPowerSeries.X : Fin d → S))
          IsDomain S ∧ IsRegularLocalRing S ∧ IsAdicComplete (maximalIdeal S) S ∧
          CharZero S ∧ CharP (ResidueField S) p ∧
          ringKrullDim S = ((d + 1 : ℕ) : WithBot ℕ∞) ∧
          maximalIdeal S = Ideal.span {(p : S)} ⊔ J ∧
          (p : S) ∉ maximalIdeal S ^ 2 ∧
          ∃ F : S →+* R, ∃ hF : IsLocalHom F,
            letI : IsLocalHom F := hF
            Function.Surjective F ∧
            @Continuous S R (maximalIdeal S).adicTopology (maximalIdeal R).adicTopology F ∧
            (∀ a : V, F (MvPowerSeries.C a) = φ a) ∧
            (∀ i, F (MvPowerSeries.X i) = x i) ∧
            Function.Bijective (ResidueField.map F) ∧
            (∀ g : S, residue R (F g) = e (residue V (MvPowerSeries.constantCoeff g))) ∧
            ∃ f : S, f ∈ J ^ 2 ∧
              let h := (p : S) - f
              let I := Ideal.span {h}
              h ∈ S⁰ ∧ h ∈ maximalIdeal S ∧ h ∉ maximalIdeal S ^ 2 ∧
              RingHom.ker F = I ∧ IsRegularLocalRing (S ⧸ I) ∧ IsDomain (S ⧸ I) ∧
              ringKrullDim (S ⧸ I) = (d : WithBot ℕ∞) ∧
              ∃ E : (S ⧸ I) ≃+* R, ∀ g : S, E (Ideal.Quotient.mk I g) = F g

end Specs.CommutativeAlgebraNotes.CoefficientRings
