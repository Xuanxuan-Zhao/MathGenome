import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Multiplicative.AffineWeilRestriction
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Reductive.GeometricRadicals
import Mathlib.FieldTheory.Separable

open CategoryTheory

universe u

namespace LinearAlgebraicGroups.Specs.FunctionFieldWeilGroupStructure

open GeometricRadicals (IsSemisimple)

/-- There is no closed split torus of positive rank over the ground field. -/
def IsAnisotropic {k : Type u} [Field k] (G : AffineAlgebraicGroup k) : Prop :=
  ¬ ∃ (S : ClosedSubgroup G.val) (r : ℕ), 0 < r ∧
    Nonempty (S.group ≅
      (StandardGroups.multiplicativePowerGroup k (ULift.{u} (Fin r))).val)

/-- The represented Weil restriction along a finite separable extension
preserves semisimplicity. -/
def WeilRestrictionPreservesSemisimplicity : Prop :=
  ∀ {k K : Type u} [Field k] [Field K] [Algebra k K] [Module.Finite k K]
    [Algebra.IsSeparable k K] (G : AffineAlgebraicGroup K) (W : AffineAlgebraicGroup k),
    ((groupPointsFunctor k).obj W.val ≅
      WeilRestriction.extendScalars k K ⋙ (groupPointsFunctor K).obj G.val) →
    IsSemisimple G → IsSemisimple W

/-- The represented Weil restriction along a finite separable extension
preserves the absence of positive-rank closed split tori. -/
def WeilRestrictionPreservesAnisotropy : Prop :=
  ∀ {k K : Type u} [Field k] [Field K] [Algebra k K] [Module.Finite k K]
    [Algebra.IsSeparable k K] (G : AffineAlgebraicGroup K) (W : AffineAlgebraicGroup k),
    ((groupPointsFunctor k).obj W.val ≅
      WeilRestriction.extendScalars k K ⋙ (groupPointsFunctor K).obj G.val) →
    IsAnisotropic G → IsAnisotropic W

end LinearAlgebraicGroups.Specs.FunctionFieldWeilGroupStructure
