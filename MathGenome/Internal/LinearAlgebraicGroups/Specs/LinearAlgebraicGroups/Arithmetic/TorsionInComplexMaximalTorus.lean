import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Classification.Pinning
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Solvable.EquivariantUnipotentSeries
import Mathlib.Analysis.Complex.Basic
import Mathlib.GroupTheory.OrderOfElement

open AlgebraicGeometry CategoryTheory
open scoped CategoryTheory.MonObj

namespace LinearAlgebraicGroups.Specs.TorsionInComplexMaximalTorus

open EquivariantUnipotentSeries (GroupPoints)
open GeometricRadicals (IsReductive)
open Pinning (SplitBorelPair)

/-- Every finite-order complex point of a connected reductive group belongs
to the maximal torus of a split Borel pair in that group. -/
def Statement : Prop :=
  ∀ (H : AffineAlgebraicGroup ℂ), IsReductive H →
    ∀ (t : GroupPoints H.val (CommAlgCat.of ℂ ℂ)), IsOfFinOrder t →
      ∃ (P : SplitBorelPair ℂ) (hP : P.G = H)
        (s : GroupPoints P.T.group (CommAlgCat.of ℂ ℂ)),
        (hP ▸ (s ≫ P.T.inclusion.hom.hom) : GroupPoints H.val (CommAlgCat.of ℂ ℂ)) = t

end LinearAlgebraicGroups.Specs.TorsionInComplexMaximalTorus
