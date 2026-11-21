import MathGenome.Internal.LieAlgebrasAndRepresentations.Specs.LieAlgebrasAndRepresentations.SolvableRadical

/-! LA-I06, Lie volume, expanded lines 4232–4265. The semidirect product is
expressed by a vector-space complement to the actual radical ideal. The
isomorphism is the restriction of the canonical quotient map. No algebraic
closure, nonzero radical, or nonsolvability assumption is imposed. -/
universe u v
namespace Specs.LieAlgebrasAndRepresentations.LeviDecomposition

def leviDecompositionType : Prop :=
  ∀ (k : Type u) (L : Type v) [Field k] [CharZero k]
    [LieRing L] [LieAlgebra k L] [FiniteDimensional k L],
    ∃ S : LieSubalgebra k L,
      SolvableRadical.IsSemisimple_value k S ∧
      IsCompl S.toSubmodule (SolvableRadical.radical_value k L).toSubmodule ∧
      ∃ e : S ≃ₗ⁅k⁆ (L ⧸ SolvableRadical.radical_value k L),
        ∀ x : S, e x = LieSubmodule.Quotient.mk (x : L)

end Specs.LieAlgebrasAndRepresentations.LeviDecomposition
