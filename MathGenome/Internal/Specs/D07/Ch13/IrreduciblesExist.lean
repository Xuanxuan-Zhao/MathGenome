import Mathlib.Algebra.Polynomial.Degree.Defs
import Mathlib.Algebra.Polynomial.Monic

/-!
Independent statement for K07.13.irreducibles_exist (paper.tex:3990–3997).
The coefficient field K is the fixed finite base field itself. Universality in
finite K includes every q = p^r, r ≥ 1, without choosing an unrelated copy.
For positive n, natural degree n is exactly polynomial degree n; the zero
polynomial cannot witness this conclusion.
-/

universe u

namespace Specs.D07.Ch13.IrreduciblesExist

/-- Every positive degree occurs among monic irreducible polynomials over the
specified finite field. Finiteness is of the underlying field, not its degree
over an unspecified smaller field. -/
def MonicIrreducibleOfEveryPositiveDegree : Prop :=
  ∀ (K : Type u) [Field K] [Finite K] (n : ℕ), 1 ≤ n →
    ∃ f : Polynomial K, f.Monic ∧ Irreducible f ∧ f.natDegree = n

end Specs.D07.Ch13.IrreduciblesExist
