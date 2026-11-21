import Mathlib.RingTheory.Algebraic.Defs
import Mathlib.Algebra.Algebra.Tower

/-!
Independent specification for K07.12.algebraic_tower
(paper.tex:3655–3662; chapters/M07.12.tex:114–121).

The three `Algebra` structures specify the embeddings. `IsScalarTower`
expresses their compatibility. Algebraicity means that each element has a
nonzero annihilating polynomial over the stated base, as in the canonical
definition used by Specs.D07.Ch12.AlgebraicDefinition. The fields and their
universes are arbitrary; no finite-degree or algebraic-closedness hypothesis
is imposed.
-/

universe u v w

namespace Specs.D07.Ch12.AlgebraicTower

/-- Algebraic extensions compose in any compatible field tower. -/
def AlgebraicityTransitive : Prop :=
  ∀ (K : Type u) (E : Type v) (L : Type w)
    [Field K] [Field E] [Field L]
    [Algebra K E] [Algebra E L] [Algebra K L] [IsScalarTower K E L],
    Algebra.IsAlgebraic K E → Algebra.IsAlgebraic E L → Algebra.IsAlgebraic K L

end Specs.D07.Ch12.AlgebraicTower
