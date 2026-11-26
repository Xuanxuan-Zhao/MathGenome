import Mathlib.Algebra.CharP.Defs
import Mathlib.RingTheory.AdicCompletion.Basic
import Mathlib.RingTheory.LocalRing.ResidueField.Defs
import Mathlib.RingTheory.MvPowerSeries.Basic
import Mathlib.RingTheory.RegularLocalRing.Defs

namespace Specs.CommutativeAlgebraNotes.CoefficientRings.EqualCharacteristicRegularPresentation

open IsLocalRing

/-- A chosen coefficient section and a generating family of size equal to the
dimension extend to a power-series presentation. -/
def PresentationOfGenerators : Prop :=
  ∀ (R : Type*) [CommRing R] [IsRegularLocalRing R] [IsAdicComplete (maximalIdeal R) R]
    (d : ℕ), ringKrullDim R = d →
    ∀ (σ : ResidueField R →+* R), (residue R).comp σ = RingHom.id (ResidueField R) →
    ∀ (x : Fin d → R), Ideal.span (Set.range x) = maximalIdeal R →
      ∃ e : MvPowerSeries (Fin d) (ResidueField R) ≃+* R,
        (∀ a, e (MvPowerSeries.C a) = σ a) ∧
        (∀ i, e (MvPowerSeries.X i) = x i) ∧
        ∀ f, residue R (e f) = MvPowerSeries.constantCoeff f

/-- A complete regular local ring of equal characteristic and Krull dimension
`d` is a power-series ring in `d` variables over its residue field. -/
def Presentation : Prop :=
  ∀ (R : Type*) [CommRing R] [IsRegularLocalRing R] [IsAdicComplete (maximalIdeal R) R]
    (d : ℕ), ringKrullDim R = d →
    ringChar (ResidueField R) = ringChar R →
      ∃ σ : ResidueField R →+* R, (residue R).comp σ = RingHom.id (ResidueField R) ∧
        ∃ e : MvPowerSeries (Fin d) (ResidueField R) ≃+* R,
          (∀ a, e (MvPowerSeries.C a) = σ a) ∧
          ∀ f, residue R (e f) = MvPowerSeries.constantCoeff f

end Specs.CommutativeAlgebraNotes.CoefficientRings.EqualCharacteristicRegularPresentation
