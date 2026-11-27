import MathGenome.Internal.HomologicalAlgebraDeepening.Specs.DerivedFormalization.CochainModels
import MathGenome.Internal.HomologicalAlgebraDeepening.Specs.DerivedFormalization.SemifreeFiltration

/-! K-flatness of a cochain complex with an exhaustive semifree filtration. -/

namespace Specs.DerivedFormalization.SemifreeFlatness

open Specs.DerivedFormalization.Cochains (compValue)
open Specs.DerivedFormalization.CochainModels (isKFlatValue)
open Specs.DerivedFormalization.SemifreeFiltration (Filtration)

universe u

/-- Any chosen semifree filtration implies K-flatness over the base ring. -/
def filtrationIsKFlatType : Prop :=
  ∀ {R : Type u} [CommRing R] {F : compValue.{u} R},
    Filtration F → isKFlatValue F

end Specs.DerivedFormalization.SemifreeFlatness
