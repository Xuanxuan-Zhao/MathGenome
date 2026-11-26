import Mathlib.RingTheory.AdicCompletion.Basic
import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.RingTheory.MvPowerSeries.Inverse
import Mathlib.RingTheory.RegularLocalRing.Defs

namespace Specs.CommutativeAlgebraNotes.CompleteRegularPowerSeries

open IsLocalRing

/-- The maximal-ideal filtration records coefficient order plus monomial degree. -/
def MaximalIdealPower : Prop :=
  ∀ (D : Type*) [CommRing D] [IsLocalRing D] (s n : ℕ)
    (f : MvPowerSeries (Fin s) D),
    f ∈ maximalIdeal (MvPowerSeries (Fin s) D) ^ n ↔
      ∀ a : Fin s →₀ ℕ, MvPowerSeries.coeff a f ∈ maximalIdeal D ^ (n - a.degree)

/-- Formal power series over a field, including the case of zero variables. -/
def OverField : Prop :=
  ∀ (D : Type*) [Field D] (s : ℕ),
    let A := MvPowerSeries (Fin s) D
    let S := Set.range (MvPowerSeries.X : Fin s → A)
    IsDomain A ∧ IsRegularLocalRing A ∧ IsAdicComplete (maximalIdeal A) A ∧
      maximalIdeal A = Ideal.span S ∧
      ringKrullDim A = s ∧ (maximalIdeal A).spanFinrank = s ∧
      (∀ T ⊂ S, Ideal.span T ≠ maximalIdeal A) ∧
      ∃ e : ResidueField A ≃+* D, ∀ f : A,
        e (residue A f) = MvPowerSeries.constantCoeff f

/-- Formal power series over a complete DVR with any chosen uniformizer. -/
def OverCompleteDVR : Prop :=
  ∀ (D : Type*) [CommRing D] [IsDomain D] [IsDiscreteValuationRing D]
    [IsAdicComplete (maximalIdeal D) D] (π : D), Irreducible π → ∀ s : ℕ,
    let A := MvPowerSeries (Fin s) D
    let S := insert (MvPowerSeries.C π) (Set.range (MvPowerSeries.X : Fin s → A))
    IsDomain A ∧ IsRegularLocalRing A ∧ IsAdicComplete (maximalIdeal A) A ∧
      maximalIdeal A = Ideal.span S ∧
      ringKrullDim A = ((s + 1 : ℕ) : WithBot ℕ∞) ∧ (maximalIdeal A).spanFinrank = s + 1 ∧
      (∀ T ⊂ S, Ideal.span T ≠ maximalIdeal A) ∧
      ∃ e : ResidueField A ≃+* ResidueField D, ∀ f : A,
        e (residue A f) = residue D (MvPowerSeries.constantCoeff f)

end Specs.CommutativeAlgebraNotes.CompleteRegularPowerSeries
