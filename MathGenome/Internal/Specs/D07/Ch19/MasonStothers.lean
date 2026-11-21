import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.RingTheory.Radical.Basic

/-!
Independent specification for K07.19.mason_stothers,
paper.tex:5734–5775 (chapters/M07.19.tex:502–543).

`radical` is the canonical UFD radical. The first interface identifies its
finite factor set with exactly the monic irreducible divisors, so its product
has each distinct factor once. The constant interface includes every nonzero
constant. No splitting field or algebraic closedness is assumed.

All three input polynomials and their radical are nonzero. Consequently their
ordinary degrees are their `natDegree`s. Nonconstancy means precisely that
there is no triple of scalars presenting all three as constant polynomials.
The characteristic-zero field and all three pairwise coprimality hypotheses
are retained explicitly.
-/

open Polynomial UniqueFactorizationMonoid
open scoped Classical

universe u

namespace Specs.D07.Ch19.MasonStothers

/-- The finite set contains exactly the distinct monic irreducible factors,
and its product is the radical appearing in the degree bound. -/
def RadicalFactors : Prop :=
  ∀ (F : Type u) [Field F] (f : Polynomial F), f ≠ 0 →
    (∀ p : Polynomial F,
      p ∈ primeFactors f ↔ Irreducible p ∧ p.Monic ∧ p ∣ f) ∧
    radical f = ∏ p ∈ primeFactors f, p

/-- The product for a nonzero constant is the empty product, namely one. -/
def RadicalConstant : Prop :=
  ∀ (F : Type u) [Field F] (x : F), x ≠ 0 → radical (C x) = 1

/-- The three degree inequalities before combining them into a maximum. -/
def MasonStothersBounds : Prop :=
  ∀ (F : Type u) [Field F] [CharZero F] (a b c : Polynomial F),
    a ≠ 0 → b ≠ 0 → c ≠ 0 →
    IsCoprime a b → IsCoprime a c → IsCoprime b c →
    a + b = c →
    (¬ ∃ x y z : F, a = C x ∧ b = C y ∧ c = C z) →
    a.natDegree + 1 ≤ (radical (a * b * c)).natDegree ∧
    b.natDegree + 1 ≤ (radical (a * b * c)).natDegree ∧
    c.natDegree + 1 ≤ (radical (a * b * c)).natDegree

/-- The paper's full polynomial abc inequality, in ordinary natural degrees. -/
def MasonStothersInequality : Prop :=
  ∀ (F : Type u) [Field F] [CharZero F] (a b c : Polynomial F),
    a ≠ 0 → b ≠ 0 → c ≠ 0 →
    IsCoprime a b → IsCoprime a c → IsCoprime b c →
    a + b = c →
    (¬ ∃ x y z : F, a = C x ∧ b = C y ∧ c = C z) →
    max a.natDegree (max b.natDegree c.natDegree) ≤
      (radical (a * b * c)).natDegree - 1

end Specs.D07.Ch19.MasonStothers
