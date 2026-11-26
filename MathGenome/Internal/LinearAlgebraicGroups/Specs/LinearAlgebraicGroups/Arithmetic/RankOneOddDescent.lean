import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Multiplicative.CharacterDescent
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Reductive.GeometricBorelConjugacy

open CategoryTheory

universe u

namespace LinearAlgebraicGroups.Specs.Arithmetic.RankOneOddDescent

open CharacterDescent (Cocharacter)
open GeometricBorelConjugacy (IsQuasiSplit)
open StandardGroups (specialLinearPoints)
open Unipotent (baseChangedAlgebraicGroup)

/-- A form of split SL₂ that is quasi-split after a separable odd-degree
extension has a noncentral cocharacter over the original field. -/
def RankOneDescent : Prop :=
  ∀ (F E K : Type u) [Field F] [Field E] [Field K] [Algebra F E] [Algebra F K]
    [Module.Finite F E] [Algebra.IsSeparable F E] [FiniteDimensional F K] [IsGalois F K],
    Odd (Module.finrank F E) →
    ∀ H : AffineAlgebraicGroup F,
      Nonempty ((groupPointsFunctor K).obj ((groupBaseChange F K).obj H.val) ≅
        specialLinearPoints K (ULift.{u} (Fin 2))) →
      IsQuasiSplit (baseChangedAlgebraicGroup E H) →
      ∃ (c : Cocharacter H.val) (Y : SchemeOver F) (g : Y ⟶ H.val.X), ¬ Centralizes c g

end LinearAlgebraicGroups.Specs.Arithmetic.RankOneOddDescent
