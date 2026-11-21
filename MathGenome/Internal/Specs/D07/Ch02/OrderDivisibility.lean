import MathGenome.Internal.Specs.D07.Ch02.ElementOrder

/-!
Independent specification of `K07.02.order_divisibility`
(paper.tex:432–443, chapters/M07.02.tex:10–21).

The carrier and group are arbitrary. Finite order is a positive natural
number `n`, equal to the canonical `orderOf x` from the upstream specification.
Divisibility of integer exponents is divisibility in `ℤ`, with `n` cast to `ℤ`.
Infinite order is represented separately by `orderOf x = 0`.
-/

namespace Specs.D07.Ch02.OrderDivisibility

universe u

/-- For an element of finite order `n`, exactly its integer multiples
annihilate the element. Negative and zero exponents are included. -/
def FinitePowerEqOneIff : Prop :=
  ∀ (G : Type u) [Group G] (x : G) (n : ℕ),
    0 < n → orderOf x = n → ∀ k : ℤ,
      x ^ k = 1 ↔ (n : ℤ) ∣ k

/-- Powers of an element of finite order agree precisely when its order
divides the difference of their integer exponents. -/
def FinitePowersEqIff : Prop :=
  ∀ (G : Type u) [Group G] (x : G) (n : ℕ),
    0 < n → orderOf x = n → ∀ a b : ℤ,
      x ^ a = x ^ b ↔ (n : ℤ) ∣ a - b

/-- For an infinite-order element, equality of integer powers is equivalent
to equality of exponents; no finiteness of the group is assumed. -/
def InfinitePowersEqIff : Prop :=
  ∀ (G : Type u) [Group G] (x : G),
    orderOf x = 0 → ∀ a b : ℤ, x ^ a = x ^ b ↔ a = b

end Specs.D07.Ch02.OrderDivisibility
