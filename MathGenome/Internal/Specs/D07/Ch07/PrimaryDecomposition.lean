import MathGenome.Internal.Specs.D07.Ch07.PrimarySubgroups
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-! Independent statements for K07.07.primary_decomposition (paper.tex:3406).
The index is precisely the finite set of prime divisors of the group order.
No nontriviality assumption is imposed; order one gives the empty product.
`Nat.factorization` supplies the exponents in the unique prime factorization.
-/
noncomputable section
namespace Specs.D07.Ch07.PrimaryDecomposition
universe u v
open scoped BigOperators

abbrev PrimeDivisors (A : Type u) := (Nat.card A).primeFactors

abbrev Primary (A : Type u) [AddCommGroup A] (p : ℕ) :=
  Specs.D07.Ch07.PrimarySubgroups.primarySubgroupValue A p

/-- The isomorphism is the addition of the component inclusions. -/
def CanonicalDecomposition : Prop :=
  ∀ (A : Type u) [AddCommGroup A] [Finite A],
    ∃ e : ((p : PrimeDivisors A) → Primary A p.val) ≃+ A,
      ∀ x, e x = ∑ p : PrimeDivisors A, (x p : A)

/-- Also applies to primes absent from the factorization, with exponent zero. -/
def PrimaryCardinality : Prop :=
  ∀ (A : Type u) [AddCommGroup A] [Finite A] (p : ℕ), p.Prime →
    Nat.card (Primary A p) = p ^ (Nat.card A).factorization p

/-- Components are intrinsic: every additive isomorphism carries each one
onto the component with the same prime in its target. -/
def PrimaryIntrinsic : Prop :=
  ∀ (A : Type u) (B : Type v) [AddCommGroup A] [AddCommGroup B]
    (e : A ≃+ B) (p : ℕ), p.Prime →
      (Primary A p).map e.toAddMonoidHom = Primary B p

end Specs.D07.Ch07.PrimaryDecomposition
