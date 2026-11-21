import MathGenome.Internal.AlgebraCore.Specs.P103.Ch05.IrreducibleIntersections
import MathGenome.Internal.AlgebraCore.Specs.P103.Ch05.PrimarySubmodules
import Mathlib.RingTheory.IsPrimary

/-! The two primary stages of Theorem 5.5 (paper.tex:1014–1016).
Primary means uniform nilpotence on the whole quotient. The finite-family
assertion does not need Noetherian or finite-generation hypotheses.
The nonempty condition excludes the empty intersection, which is not proper. -/

namespace P103.Specs.Ch05.IrreduciblePrimary

universe u v w
open P103.Specs.Ch05.IrreducibleIntersections
open P103.Specs.Ch05.PrimarySubmodules

/-- The library uses the same uniform primary condition; its exponent may
be zero, which can always be increased to a positive exponent. -/
def primary_iff_mathlibType : Prop :=
  ∀ (R : Type u) [CommRing R] (M : Type v) [AddCommGroup M] [Module R M]
    (N : Submodule R M), primaryValue R M N ↔ N.IsPrimary

def irreducible_primaryType : Prop :=
  ∀ (R : Type u) [CommRing R] [IsNoetherianRing R]
    (M : Type v) [AddCommGroup M] [Module R M] [Module.Finite R M]
    (N : Submodule R M), IsIrreducible N → primaryValue R M N

/-- In the nonzero quotient every scalar killing a nonzero vector has a
positive power annihilating every vector, with one common exponent. -/
def irreducible_quotient_nilpotentType : Prop :=
  ∀ (R : Type u) [CommRing R] [IsNoetherianRing R]
    (M : Type v) [AddCommGroup M] [Module R M] [Module.Finite R M]
    (N : Submodule R M), IsIrreducible N →
    Nontrivial (M ⧸ N) ∧
      ∀ (r : R) (x : M ⧸ N), r • x = 0 → x ≠ 0 →
        ∃ n : ℕ, 1 ≤ n ∧ ∀ y : M ⧸ N, r ^ n • y = 0

/-- Finite nonempty intersections preserve being primary for the specified
proper prime, including equality of the resulting annihilator radical. -/
def finite_intersection_primaryType : Prop :=
  ∀ (R : Type u) [CommRing R] (M : Type v) [AddCommGroup M] [Module R M]
    (ι : Type w) (s : Finset ι) (Q : ι → Submodule R M) (p : Ideal R),
    s.Nonempty → p.IsPrime →
    (∀ i ∈ s, primaryValue R M (Q i) ∧ radicalValue R M (Q i) = p) →
    primaryValue R M (⨅ i ∈ s, Q i) ∧ radicalValue R M (⨅ i ∈ s, Q i) = p

end P103.Specs.Ch05.IrreduciblePrimary
