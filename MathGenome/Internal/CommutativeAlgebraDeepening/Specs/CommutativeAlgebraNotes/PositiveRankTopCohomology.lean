import MathGenome.Internal.CommutativeAlgebraDeepening.Specs.CommutativeAlgebraNotes.IdealTorsion
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.TensorProduct.Defs
import Mathlib.RingTheory.AdicCompletion.Basic
import Mathlib.RingTheory.KrullDimension.Basic
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.RingTheory.Noetherian.Basic

open CategoryTheory IsLocalRing
open scoped TensorProduct

namespace Specs.CommutativeAlgebraNotes.PositiveRankTopCohomology

universe u

/-- A finite module of positive rank over a complete Noetherian local domain
has nonzero local cohomology supported at the maximal ideal in the ring's
Krull dimension. Rank is the dimension after base change to the fraction field. -/
def PositiveRankNonvanishing : Prop :=
  ∀ {B : Type u} [CommRing B] [IsLocalRing B] [IsDomain B] [IsNoetherianRing B]
    [IsAdicComplete (maximalIdeal B) B] (d : ℕ),
    ringKrullDim B = (d : WithBot ℕ∞) →
    ∀ (N : ModuleCat.{u} B) [Module.Finite B N],
      0 < Module.finrank (FractionRing B) (FractionRing B ⊗[B] N) →
      Nontrivial ((IdealTorsion.localCohomology (maximalIdeal B) (d : ℤ)).obj N)

end Specs.CommutativeAlgebraNotes.PositiveRankTopCohomology
