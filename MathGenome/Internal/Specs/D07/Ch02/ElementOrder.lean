import MathGenome.Internal.Specs.D07.Ch01.IntegerPowerLaws
import Mathlib.GroupTheory.OrderOfElement

/-!
Independent specification of `K07.02.element_order`
(paper.tex:429–431, chapters/M07.02.tex:7–9).

The same arbitrary multiplicative group as in the upstream specifications
is used here. The natural number `orderOf x` encodes infinity by zero.
Its positive values are exactly the least positive annihilating exponents;
zero is characterized separately, without claiming a positive annihilator.
No finiteness, commutativity, or nontriviality of the group is assumed.
-/

namespace Specs.D07.Ch02.ElementOrder

universe u

/-- The type of natural-valued element-order functions on arbitrary groups. -/
def ElementOrderType : Type (u + 1) :=
  ∀ (G : Type u) [Group G], G → ℕ

/-- Canonical element order, with zero denoting infinite order. -/
noncomputable def elementOrderValue : ElementOrderType.{u} :=
  fun _ _ x => orderOf x

/-- A positive value exists precisely when a positive power is the identity. -/
def FiniteOrderIff : Prop :=
  ∀ (G : Type u) [Group G] (x : G),
    0 < orderOf x ↔ ∃ n : ℕ, 0 < n ∧ x ^ n = 1

/-- For every positive `n`, order `n` means that `n` is the least positive
annihilating exponent, in both directions. -/
def LeastPositiveExponent : Prop :=
  ∀ (G : Type u) [Group G] (x : G) (n : ℕ), 0 < n →
    (orderOf x = n ↔
      x ^ n = 1 ∧ ∀ m : ℕ, 0 < m → x ^ m = 1 → n ≤ m)

/-- Zero denotes exactly the case with no positive annihilating exponent. -/
def InfiniteOrderIff : Prop :=
  ∀ (G : Type u) [Group G] (x : G),
    orderOf x = 0 ↔ ∀ n : ℕ, 0 < n → x ^ n ≠ 1

/-- Order one is precisely the identity, including in the trivial group. -/
def OrderOneIff : Prop :=
  ∀ (G : Type u) [Group G] (x : G), orderOf x = 1 ↔ x = 1

end Specs.D07.Ch02.ElementOrder
