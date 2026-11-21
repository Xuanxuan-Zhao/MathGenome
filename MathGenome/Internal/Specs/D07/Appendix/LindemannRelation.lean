import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Algebra.Algebra.Rat
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Algebra.BigOperators.Fin

/-!
Independent statements of `lem:lindemann-special-relation`, paper.tex:7675.
Rationality concerns the complete monic root product. Lists retain repeated
entries, and the empty list is permitted. Positive natural numbers represent
the positive integers in the conclusion.
-/

namespace Specs.D07.Appendix.LindemannRelation

open Polynomial

/-- No positive integer plus the exponential sum of this root multiset vanishes. -/
def SpecialRelation : Prop :=
  ∀ (β : List ℂ) (P : ℚ[X]),
    (∀ b ∈ β, b ≠ 0) →
    P.map (algebraMap ℚ ℂ) = (β.map (fun b => X - C b)).prod →
    ∀ k : ℕ, 0 < k → (k : ℂ) + (β.map Complex.exp).sum ≠ 0

/-- The equivalent formulation for a family indexed by `Fin m`, including m = 0. -/
def SpecialRelationFin : Prop :=
  ∀ (m : ℕ) (β : Fin m → ℂ) (P : ℚ[X]),
    (∀ j, β j ≠ 0) →
    P.map (algebraMap ℚ ℂ) = ∏ j, (X - C (β j)) →
    ∀ k : ℕ, 0 < k → (k : ℂ) + ∑ j, Complex.exp (β j) ≠ 0

end Specs.D07.Appendix.LindemannRelation
