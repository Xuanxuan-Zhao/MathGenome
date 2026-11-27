import MathGenome.Internal.HomologicalAlgebraDeepening.Specs.DerivedFormalization.Affine.SemifreeAlgebras
import MathGenome.Internal.HomologicalAlgebraDeepening.Specs.DerivedFormalization.Affine.Tensor

open CategoryTheory

universe u v

namespace Specs.DerivedFormalization.Affine.SemifreeFlatness

open _root_.DerivedFormalization.Affine (NonpositiveCDGA)
open _root_.DerivedFormalization.Affine.Semifree (IsSemifree)
open Specs.DerivedFormalization.Affine.Tensor (ModuleTensor regular restrict)

/-- A semifree algebra extension is K-flat as a dg module over the original
base algebra, with its action given by restriction of scalars. -/
def SemifreeAlgebraKFlat : Prop :=
  ∀ {k : Type u} [Field k] [CharZero k] (T : ModuleTensor.{u,v} k)
    {A P : NonpositiveCDGA.{u,v} k} (f : A ⟶ P),
    T.Formulas (𝟙 A.toCommDGAlgebra) (restrict f (regular P.toCommDGAlgebra)) →
    IsSemifree A f →
    T.KFlat (restrict f (regular P.toCommDGAlgebra))

end Specs.DerivedFormalization.Affine.SemifreeFlatness
