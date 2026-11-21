import MathGenome.Internal.Specs.D07.Ch02.OrderDivisibility
import MathGenome.Internal.Specs.D07.Foundations.IntegerArithmetic

/-!
Independent specification of `K07.02.order_of_power`
(paper.tex:469–479, chapters/M07.02.tex:47–57).

The carrier is an arbitrary group; neither finiteness nor commutativity is
assumed. A finite element order is a positive natural number, and zero
encodes infinite order as in the upstream `ElementOrder` specification.
Integer absolute value is represented by `Int.natAbs`, so the gcd and the
exact quotient in the finite-order formula are natural numbers. All integer
exponents, including zero and negative exponents, occur in that formula.
-/

namespace Specs.D07.Ch02.OrderOfPower

universe u

/-- The order of any integer power of an element of finite order. -/
def FiniteOrderOfPower : Prop :=
  ∀ (G : Type u) [Group G] (x : G) (n : ℕ),
    0 < n → orderOf x = n → ∀ k : ℤ,
      orderOf (x ^ k) = n / Nat.gcd n k.natAbs

/-- The zeroth power of an infinite-order element has order one. -/
def InfiniteOrderZeroPower : Prop :=
  ∀ (G : Type u) [Group G] (x : G),
    orderOf x = 0 → orderOf (x ^ (0 : ℤ)) = 1

/-- Every nonzero integer power of an infinite-order element has infinite order. -/
def InfiniteOrderNonzeroPower : Prop :=
  ∀ (G : Type u) [Group G] (x : G),
    orderOf x = 0 → ∀ k : ℤ, k ≠ 0 → orderOf (x ^ k) = 0

end Specs.D07.Ch02.OrderOfPower
