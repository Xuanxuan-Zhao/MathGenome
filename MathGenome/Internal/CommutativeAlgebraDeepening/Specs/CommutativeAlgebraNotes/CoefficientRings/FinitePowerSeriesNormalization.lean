import Mathlib.RingTheory.AdicCompletion.Basic
import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.RingTheory.LocalRing.ResidueField.Basic
import Mathlib.RingTheory.MvPowerSeries.Inverse
import Mathlib.RingTheory.RegularLocalRing.Defs

namespace Specs.CommutativeAlgebraNotes.CoefficientRings.FinitePowerSeriesNormalization

open IsLocalRing

universe u v

/-- The properties of the local inclusion of a power-series normalization. -/
def IsFiniteNormalization {S : Type u} {B : Type v}
    [CommRing S] [IsLocalRing S] [CommRing B] [IsLocalRing B]
    (d : ℕ) (F : S →+* B) : Prop :=
  ∃ hF : IsLocalHom F,
    letI : IsLocalHom F := hF
    letI : Algebra S B := F.toAlgebra
    IsDomain S ∧ IsRegularLocalRing S ∧ IsAdicComplete (maximalIdeal S) S ∧
      ringKrullDim S = (d : WithBot ℕ∞) ∧ Function.Injective F ∧
      Function.Bijective (ResidueField.map F) ∧ Module.Finite S B ∧
      ((maximalIdeal S).map F).radical = maximalIdeal B

/-- In equal characteristic the variables map to a system of parameters of
the domain, and the residue map is given by the constant term. -/
def EqualCharacteristicWitness (B : Type u) [CommRing B] [IsLocalRing B] (d : ℕ) : Prop :=
  let k := ResidueField B
  let S := MvPowerSeries (Fin d) k
  ∃ (σ : k →+* B) (x : Fin d → B) (F : S →+* B),
    (residue B).comp σ = RingHom.id k ∧
    (∀ i, x i ∈ maximalIdeal B) ∧ (Ideal.span (Set.range x)).radical = maximalIdeal B ∧
    (∀ a, F (MvPowerSeries.C a) = σ a) ∧ (∀ i, F (MvPowerSeries.X i) = x i) ∧
    (∀ f : S, residue B (F f) = MvPowerSeries.constantCoeff f) ∧
    IsFiniteNormalization d F

/-- In mixed characteristic the coefficients come from a complete DVR with
uniformizer p, and the variables map to lifts of parameters of the reduction
modulo p. The residue identification is the one on the coefficient DVR. -/
def MixedCharacteristicWitness (B : Type u) [CommRing B] [IsLocalRing B] (d p : ℕ) : Prop :=
  let I : Ideal B := Ideal.span {(p : B)}
  let Q := B ⧸ I
  ∃ hQ : IsLocalRing Q,
    letI : IsLocalRing Q := hQ
    (p : B) ≠ 0 ∧ Function.Injective (fun b : B => (p : B) * b) ∧
    ringKrullDim Q = ((d - 1 : ℕ) : WithBot ℕ∞) ∧
    (∃ (Λ : Type u) (_ : CommRing Λ) (_ : IsDomain Λ) (_ : IsDiscreteValuationRing Λ),
      CharZero Λ ∧ IsAdicComplete (maximalIdeal Λ) Λ ∧
      maximalIdeal Λ = Ideal.span {(p : Λ)} ∧
      ∃ (e : ResidueField Λ ≃+* ResidueField B) (φ : Λ →+* B)
        (x : Fin (d - 1) → B) (F : MvPowerSeries (Fin (d - 1)) Λ →+* B),
        Function.Injective φ ∧ (residue B).comp φ = e.toRingHom.comp (residue Λ) ∧
        (∀ i, x i ∈ maximalIdeal B) ∧
        (Ideal.span (Set.range (Ideal.Quotient.mk I ∘ x))).radical = maximalIdeal Q ∧
        (∀ a, F (MvPowerSeries.C a) = φ a) ∧ (∀ i, F (MvPowerSeries.X i) = x i) ∧
        (∀ f, residue B (F f) = e (residue Λ (MvPowerSeries.constantCoeff f))) ∧
        IsFiniteNormalization d F)

def EqualCharacteristic : Prop :=
  ∀ (B : Type u) [CommRing B] [IsLocalRing B] [IsDomain B] [IsNoetherianRing B]
    [IsAdicComplete (maximalIdeal B) B] (d : ℕ),
    ringKrullDim B = (d : WithBot ℕ∞) →
    ringChar (ResidueField B) = ringChar B →
    EqualCharacteristicWitness B d

def MixedCharacteristic : Prop :=
  ∀ (B : Type u) [CommRing B] [IsLocalRing B] [IsDomain B] [IsNoetherianRing B]
    [IsAdicComplete (maximalIdeal B) B] [CharZero B] (d p : ℕ),
    ringKrullDim B = (d : WithBot ℕ∞) →
    p.Prime → ∀ [CharP (ResidueField B) p], MixedCharacteristicWitness B d p

def Normalization : Prop :=
  ∀ (B : Type u) [CommRing B] [IsLocalRing B] [IsDomain B] [IsNoetherianRing B]
    [IsAdicComplete (maximalIdeal B) B],
    ∃ d : ℕ, ringKrullDim B = (d : WithBot ℕ∞) ∧
      ((ringChar (ResidueField B) = ringChar B ∧ EqualCharacteristicWitness B d) ∨
      ∃ p : ℕ, p.Prime ∧ CharZero B ∧ CharP (ResidueField B) p ∧ MixedCharacteristicWitness B d p)

end Specs.CommutativeAlgebraNotes.CoefficientRings.FinitePowerSeriesNormalization
