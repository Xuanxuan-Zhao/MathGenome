import Mathlib.Basic.Complex.Basic
import Mathlib.Algebra.Polynomial.Splits
import Mathlib.LinearAlgebra.FiniteDimensional.Defs

/-!
Independent specification of paper.tex:7585–7600
(algebraic-fta.tex, `lem:complex-square-root-algebraic`).
The base is the constructed complex field, with no algebraic-closedness
hypothesis. Quadratic factors may coincide. An extension uses its specified
complex algebra structure; degree two means vector-space dimension two.
-/

universe u

namespace Specs.D07.Appendix.ComplexQuadraticExtensions

open Polynomial

def SquareRootExists : Prop :=
  ∀ z : ℂ, ∃ w : ℂ, w ^ 2 = z

def QuadraticFactorization : Prop :=
  ∀ A B D : ℂ, A ≠ 0 → ∃ r s : ℂ,
    C A * X ^ 2 + C B * X + C D = C A * (X - C r) * (X - C s)

def QuadraticSplits : Prop :=
  ∀ A B D : ℂ, A ≠ 0 → (C A * X ^ 2 + C B * X + C D).Splits

def NoQuadraticExtension : Prop :=
  ∀ (E : Type u) [Field E] [Algebra ℂ E] [FiniteDimensional ℂ E],
    Module.finrank ℂ E ≠ 2

/-- The same nonexistence statement using the manuscript's cardinal degree. -/
def NoCardinalQuadraticExtension : Prop :=
  ∀ (E : Type u) [Field E] [Algebra ℂ E], Module.rank ℂ E ≠ 2

end Specs.D07.Appendix.ComplexQuadraticExtensions
