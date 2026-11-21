import MathGenome.Internal.Specs.D07.Ch01.ElementaryGroupLaws
import Mathlib.Algebra.BigOperators.Group.List.Defs

/-!
Independent specification of `K07.01.integer_power_laws`
(paper.tex:240–251, chapters/M07.01.tex:25–36).

The power operation is the canonical integer power of the same arbitrary
`Group` used in the upstream specifications. The first three propositions
identify it with the source's conventions: repeated products for positive
exponents, the identity at zero, and powers of the inverse for negative
exponents. The remaining propositions state all four displayed laws.
No commutativity or nontriviality is imposed on the group. Only the two
specified elements need commute in the last proposition.
-/

namespace Specs.D07.Ch01.IntegerPowerLaws

universe u

/-- A positive integer power is the product of the indicated number of copies. -/
def PositivePowerProduct : Prop :=
  ∀ (G : Type u) [Group G] (x : G) (n : ℕ),
    0 < n → x ^ (n : ℤ) = (List.replicate n x).prod

/-- The zeroth power is the identity, also in the trivial group. -/
def ZeroPower : Prop :=
  ∀ (G : Type u) [Group G] (x : G), x ^ (0 : ℤ) = 1

/-- The negative-exponent convention uses the natural power of the inverse. -/
def NegativeNaturalPower : Prop :=
  ∀ (G : Type u) [Group G] (x : G) (n : ℕ),
    x ^ (-(n : ℤ)) = (x⁻¹) ^ n

def PowerAdd : Prop :=
  ∀ (G : Type u) [Group G] (x : G) (m n : ℤ),
    x ^ (m + n) = x ^ m * x ^ n

def PowerMul : Prop :=
  ∀ (G : Type u) [Group G] (x : G) (m n : ℤ),
    (x ^ m) ^ n = x ^ (m * n)

def PowerNeg : Prop :=
  ∀ (G : Type u) [Group G] (x : G) (n : ℤ),
    x ^ (-n) = (x ^ n)⁻¹

/-- Pairwise commutativity suffices; the ambient group can be nonabelian. -/
def CommutingProductPower : Prop :=
  ∀ (G : Type u) [Group G] (x y : G),
    x * y = y * x → ∀ n : ℤ, (x * y) ^ n = x ^ n * y ^ n

end Specs.D07.Ch01.IntegerPowerLaws
