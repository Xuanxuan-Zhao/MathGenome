import MathGenome.Internal.Specs.D07.Ch12.AlgebraicDefinition
import MathGenome.Internal.Specs.D07.Ch12.DegreeDefinition

/-!
Independent specification for K07.12.finite_algebraic, paper.tex:3575–3582.

The extension includes its chosen `Algebra K L` structure. Its degree is
cardinal dimension, so equality with the natural cardinal `n` supplies the
finiteness hypothesis. The witness is a nonzero formal polynomial over K,
evaluated in L through that same structure map. Its degree is bounded by n.
No algebraicity or algebraic closedness is assumed.
-/

universe u v

namespace Specs.D07.Ch12.FiniteAlgebraic

/-- The full degree-bounded annihilator assertion, including arbitrary finite n. -/
def ExistsAnnihilatingPolynomial : Prop :=
  ∀ (K : Type u) (L : Type v) [Field K] [Field L] [Algebra K L] (n : ℕ),
    Module.rank K L = (n : Cardinal.{v}) →
      ∀ α : L, ∃ f : Polynomial K,
        f ≠ 0 ∧ f.degree ≤ (n : WithBot ℕ) ∧ Polynomial.aeval α f = 0

/-- In particular, a finite extension is algebraic, with the source's meaning
of finiteness and the canonical elementwise algebraicity predicate. -/
def FiniteExtensionIsAlgebraic : Prop :=
  ∀ (K : Type u) (L : Type v) [Field K] [Field L] [Algebra K L],
    (∃ n : ℕ, Module.rank K L = (n : Cardinal.{v})) → Algebra.IsAlgebraic K L

end Specs.D07.Ch12.FiniteAlgebraic
