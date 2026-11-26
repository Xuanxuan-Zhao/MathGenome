import MathGenome.Internal.CommutativeAlgebraDeepening.Specs.CommutativeAlgebraNotes.ExcellenceDefinitions
import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.RingTheory.MvPowerSeries.NoZeroDivisors

/-! The regular power-series base case of Lemma 5.12. -/

namespace Specs.CommutativeAlgebraNotes.PolynomialCompletionsOverRegularConstants

open scoped TensorProduct
open IsLocalRing
open _root_.CommutativeAlgebraNotes.Excellence.Specs (GeometricallyRegularValue)

universe u

abbrev CompletedPolynomialStalk {S : Type u} [CommRing S]
    (P : Ideal (Polynomial S)) [P.IsPrime] :=
  AdicCompletion (maximalIdeal (Localization.AtPrime P)) (Localization.AtPrime P)

/-- The fraction field is taken on the constant ring. The polynomial prime is arbitrary. -/
abbrev GenericConstantsFibre {S : Type u} [CommRing S] [IsDomain S]
    (P : Ideal (Polynomial S)) [P.IsPrime] :=
  FractionRing S ⊗[S] CompletedPolynomialStalk P

def OverField : Prop :=
  ∀ (k : Type u) [Field k] (r : ℕ)
    (P : Ideal (Polynomial (MvPowerSeries (Fin r) k))) [P.IsPrime],
    letI : IsDomain (MvPowerSeries (Fin r) k) := NoZeroDivisors.to_isDomain _
    GeometricallyRegularValue (FractionRing (MvPowerSeries (Fin r) k))
      (GenericConstantsFibre P)

def OverCompleteDVR : Prop :=
  ∀ (D : Type u) [CommRing D] [IsDomain D] [IsDiscreteValuationRing D] [CharZero D]
    [IsAdicComplete (maximalIdeal D) D] (p : ℕ) [Fact p.Prime],
    Irreducible (p : D) → ∀ (r : ℕ)
      (P : Ideal (Polynomial (MvPowerSeries (Fin r) D))) [P.IsPrime],
      letI : IsDomain (MvPowerSeries (Fin r) D) := NoZeroDivisors.to_isDomain _
      GeometricallyRegularValue (FractionRing (MvPowerSeries (Fin r) D))
        (GenericConstantsFibre P)

end Specs.CommutativeAlgebraNotes.PolynomialCompletionsOverRegularConstants
