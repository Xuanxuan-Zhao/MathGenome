import Mathlib.Algebra.Polynomial.Degree.Defs
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Basic.ExistsUnique

/-! The field-valued residue statement of W51 (paper.tex, Hermite interpolation).
The data are arbitrary polynomial representatives of the residue classes;
no characteristic restriction or derivative interpretation is imposed. -/

namespace NumAnalysis206.Approximation.Specs

universe u

open Polynomial
open scoped BigOperators

/-- Every prescribed family of residues at distinct nodes admits exactly one
polynomial of degree less than the sum of the positive multiplicities. -/
def HermiteResidueInterpolation : Prop :=
  ∀ (K : Type u) [Field K] (s : ℕ), 0 < s →
    ∀ (x : Fin s → K), Function.Injective x →
    ∀ (m : Fin s → ℕ), (∀ i, 0 < m i) →
    ∀ (a : Fin s → K[X]),
      ∃! p : K[X], p.degree < (↑(∑ i, m i) : WithBot ℕ) ∧
        ∀ i, (X - C (x i)) ^ m i ∣ p - a i

end NumAnalysis206.Approximation.Specs
