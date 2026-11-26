import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Arithmetic.GlobalPlaces
import MathGenome.Internal.RingModuleAssociativeAlgebra.Specs.RM03.CSA.Degree

namespace LinearAlgebraicGroups.Arithmetic.AlmostEverywhereSplitAlgebras

universe u v w

/-- A central simple algebra over a global field becomes a full matrix algebra of
its degree at all but finitely many nonarchimedean places. -/
def AlmostEverywhereSplit : Prop :=
  ∀ {K : Type u} [Field K] (D : GlobalFieldData.{u, v} K)
    {A : Type w} [Ring A] [Algebra K A],
    _root_.Specs.RM03.CSA.isCentralSimple K A →
    {p : D.FinitePlace |
      letI : Algebra K (D.FiniteCompletion p) := (D.embedding (.inl p)).toAlgebra
      let n := _root_.Specs.RM03.CSA.degree K A
      ¬ Nonempty (_root_.Specs.RM03.CSA.baseChange K (D.FiniteCompletion p) A ≃ₐ[D.FiniteCompletion p]
        Matrix (Fin n) (Fin n) (D.FiniteCompletion p))}.Finite

end LinearAlgebraicGroups.Arithmetic.AlmostEverywhereSplitAlgebras
