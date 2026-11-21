import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Unbounded.SymmetryAndDeficiencies

/-! The last assertion of paper.tex:13687–13739. The index is the cardinality
of a Hilbert basis of the closed adjoint eigenspace, as in the shared Specs.
There is no separability or finite-dimensionality assumption. -/
noncomputable section
universe u
namespace ExpandedFA.Unbounded.DeficiencyHalfPlaneConstancySpec
open SymmetryAndDeficienciesSpec

def HalfPlaneConstancyExpected : Prop :=
  ∀ {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (S : Operator ℂ H H), S.IsClosed → (hS : symmetricValue S) →
    ∀ z w : ℂ,
      ((0 < z.im ∧ 0 < w.im) ∨ (z.im < 0 ∧ w.im < 0)) →
      deficiencyIndexValue S hS.1 z = deficiencyIndexValue S hS.1 w

end ExpandedFA.Unbounded.DeficiencyHalfPlaneConstancySpec
