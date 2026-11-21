import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch07.ExpConstruction

/-!
Independent specification of K03.07.exp_addition, paper.tex:1561–1579.
The function is the shared factorial-series sum, for every complex argument.
Nonvanishing is included explicitly, as established in the source proof.
-/

namespace Specs.SingleVariableAnalysis.Ch07.ExpAddition

open ExpConstruction

noncomputable def addition : Prop :=
  ∀ z w : ℂ, seriesExpValue (z + w) = seriesExpValue z * seriesExpValue w

noncomputable def zero : Prop := seriesExpValue 0 = 1

noncomputable def nonvanishing : Prop := ∀ z : ℂ, seriesExpValue z ≠ 0

noncomputable def negation : Prop :=
  ∀ z : ℂ, seriesExpValue (-z) = 1 / seriesExpValue z

end Specs.SingleVariableAnalysis.Ch07.ExpAddition
