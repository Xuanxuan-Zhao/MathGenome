import MathGenome.Internal.Specs.D07.Ch12.SplittingDefinition
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.LinearAlgebra.Dimension.Finite

/-!
Independent specification for the inequality in K07.12.splitting_degree_bound
(paper.tex:3712–3718). The chosen algebra structure specifies the base embedding.
The upstream splitting-field predicate includes f ≠ 0, splitting, and field
generation by its roots. The existential natural cardinal simultaneously states
finite degree and its factorial bound; it cannot hide infinite dimension behind
the natural-number finrank convention. Constants have natural degree zero.
No separability, characteristic, or algebraic-closedness premise is imposed.
-/

universe u v

namespace Specs.D07.Ch12.SplittingDegreeBoundFactorialInequality

/-- A splitting field of a nonzero degree-n polynomial has finite degree at
most n!, including n = 0 and polynomials with repeated roots. -/
def FactorialInequality : Prop :=
  ∀ (K : Type u) (L : Type v) [Field K] [Field L] [Algebra K L]
    (f : Polynomial K), SplittingDefinition.splittingFieldValue K L f →
      ∃ d : ℕ, Module.rank K L = (d : Cardinal.{v}) ∧ d ≤ f.natDegree.factorial

end Specs.D07.Ch12.SplittingDegreeBoundFactorialInequality
