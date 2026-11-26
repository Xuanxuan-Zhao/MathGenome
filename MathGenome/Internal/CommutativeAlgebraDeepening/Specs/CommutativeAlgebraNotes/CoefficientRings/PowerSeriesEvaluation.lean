import Mathlib.RingTheory.AdicCompletion.Topology
import Mathlib.RingTheory.LocalRing.ResidueField.Basic
import Mathlib.RingTheory.MvPowerSeries.Inverse
import Mathlib.RingTheory.Noetherian.Defs

namespace Specs.CommutativeAlgebraNotes.PowerSeriesEvaluation

open IsLocalRing

/-- A local coefficient map inducing an isomorphism of residue fields extends to
evaluation at any finite family in the target maximal ideal. This applies to a
coefficient field or a complete discrete valuation ring, including when there
are no variables. -/
def Evaluation : Prop :=
  ∀ (D R : Type*) [CommRing D] [IsLocalRing D] [CommRing R] [IsLocalRing R]
    [IsNoetherianRing R] [IsAdicComplete (maximalIdeal R) R]
    (φ : D →+* R) [IsLocalHom φ] (_ : Function.Bijective (ResidueField.map φ))
    (s : ℕ) (x : Fin s → R) (_ : ∀ i, x i ∈ maximalIdeal R),
    let S := MvPowerSeries (Fin s) D
    ∃ F : S →+* R, ∃ hF : IsLocalHom F,
      letI : IsLocalHom F := hF
      @Continuous S R (maximalIdeal S).adicTopology (maximalIdeal R).adicTopology F ∧
      (∀ d, F (MvPowerSeries.C d) = φ d) ∧
      (∀ i, F (MvPowerSeries.X i) = x i) ∧
      Function.Bijective (ResidueField.map F) ∧
      (∀ f : S, ResidueField.map F (residue S f) =
        ResidueField.map φ (residue D (MvPowerSeries.constantCoeff f))) ∧
      (maximalIdeal S).map F = (maximalIdeal D).map φ ⊔ Ideal.span (Set.range x)

end Specs.CommutativeAlgebraNotes.PowerSeriesEvaluation
