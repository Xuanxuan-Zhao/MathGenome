import MathGenome.Internal.Specs.D07.Ch12.SplittingDefinition
import Mathlib.FieldTheory.Separable
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.LinearAlgebra.Dimension.Finite

/-!
Independent specification for K07.12.splitting_degree_bound,
paper.tex:3712–3721. The chosen algebra structure specifies the embedding.
The shared splitting-field predicate includes nonzeroness, splitting, and
generation by the roots. Existential natural cardinal degrees assert finiteness
as part of each conclusion, without relying on finrank's infinite-case default.
Nonzero constants, inseparable polynomials, and arbitrary characteristics are
allowed in the inequality; only the divisibility assertion assumes separability.
-/

universe u v

namespace Specs.D07.Ch12.SplittingDegreeBound

/-- Every splitting field of a nonzero polynomial of degree n has degree ≤ n!. -/
def FactorialBound : Prop :=
  ∀ (K : Type u) (L : Type v) [Field K] [Field L] [Algebra K L]
    (f : Polynomial K), SplittingDefinition.splittingFieldValue K L f →
      ∃ d : ℕ, Module.rank K L = (d : Cardinal.{v}) ∧ d ≤ f.natDegree.factorial

/-- For separable f the finite splitting-field degree divides n!, including n = 0. -/
def FactorialDivisibility : Prop :=
  ∀ (K : Type u) (L : Type v) [Field K] [Field L] [Algebra K L]
    (f : Polynomial K), SplittingDefinition.splittingFieldValue K L f →
      f.Separable →
      ∃ d : ℕ, Module.rank K L = (d : Cardinal.{v}) ∧ d ∣ f.natDegree.factorial

end Specs.D07.Ch12.SplittingDegreeBound
