import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Arithmetic.SplitAlbertLocalForms
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Descent.RelativeRank

open scoped RatFunc

universe u v

namespace LinearAlgebraicGroups.Arithmetic.F4SplitFieldsSpecification

open LinearAlgebraicGroups.Specs
open GeometricRadicals (IsSplitTorus)
open RankOneFlag (IsGeometricallyMaximal)
open RelativeRank (relativeRank)
open SplitAlbertLocalFormsSpecification (IsAbsoluteF4)

/-- The original group contains a split geometrically maximal torus and has positive rank. -/
def HasSplitMaximalTorus {k : Type u} [Field k] (G : AffineAlgebraicGroup k) : Prop :=
  (∃ T : ClosedSubgroup G.val, IsSplitTorus T.group ∧ IsGeometricallyMaximal T) ∧
    0 < relativeRank G

/-- Every absolute type F₄ group over a nonarchimedean local field is split. -/
def LocalSplitting : Prop :=
  ∀ (k : Type u) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (G : AffineAlgebraicGroup k),
    IsAbsoluteF4 G → HasSplitMaximalTorus G

/-- Every absolute type F₄ group over a finite extension of a finite-constant
rational function field is split. -/
def FunctionFieldSplitting : Prop :=
  ∀ {k : Type u} [Field k] {F : Type v} [Field F] [Finite F]
    [Algebra F⟮X⟯ k] [FiniteDimensional F⟮X⟯ k] (G : AffineAlgebraicGroup k),
    IsAbsoluteF4 G → HasSplitMaximalTorus G

/-- The local assertion applies to every actual finite completion of a global field. -/
def FiniteCompletionSplitting : Prop :=
  ∀ {k : Type u} [Field k] (D : GlobalFieldData.{u,v} k) (w : D.FinitePlace)
    (G : AffineAlgebraicGroup (D.FiniteCompletion w)),
    IsAbsoluteF4 G → HasSplitMaximalTorus G

end LinearAlgebraicGroups.Arithmetic.F4SplitFieldsSpecification
