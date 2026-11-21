import MathGenome.Internal.Specs.D07.Ch01.GroupDefinition
import Mathlib.Basic.ExistsUnique
import Mathlib.Logic.Function.Defs

/-!
Independent specification of `K07.01.elementary_group_laws`
(paper.tex:229–243, chapters/M07.01.tex:14–28).

Every carrier and group structure is arbitrary. In particular there is no
commutativity, finiteness, or nontriviality assumption. An identity is two-sided,
as is an inverse. The multiplication maps below are maps of the carrier to itself.
-/

namespace Specs.D07.Ch01.ElementaryGroupLaws

universe u

/-- There is exactly one two-sided identity for the given multiplication. -/
def IdentityUnique : Prop :=
  ∀ (G : Type u) [Group G],
    ∃! e : G, (∀ x : G, e * x = x) ∧ (∀ x : G, x * e = x)

/-- Every element has exactly one two-sided inverse for the given identity. -/
def InverseUnique : Prop :=
  ∀ (G : Type u) [Group G] (x : G), ∃! y : G, x * y = 1 ∧ y * x = 1

/-- Multiplication on the left by any fixed element is a bijection. -/
def LeftMultiplicationBijective : Prop :=
  ∀ (G : Type u) [Group G] (a : G), Function.Bijective (fun x : G => a * x)

/-- Multiplication on the right by any fixed element is a bijection. -/
def RightMultiplicationBijective : Prop :=
  ∀ (G : Type u) [Group G] (a : G), Function.Bijective (fun x : G => x * a)

def LeftCancellation : Prop :=
  ∀ (G : Type u) [Group G] (a x y : G), a * x = a * y → x = y

def RightCancellation : Prop :=
  ∀ (G : Type u) [Group G] (a x y : G), x * a = y * a → x = y

/-- Inverting a product reverses the order of its factors. -/
def ProductInverse : Prop :=
  ∀ (G : Type u) [Group G] (x y : G), (x * y)⁻¹ = y⁻¹ * x⁻¹

def InverseInverse : Prop :=
  ∀ (G : Type u) [Group G] (x : G), (x⁻¹)⁻¹ = x

end Specs.D07.Ch01.ElementaryGroupLaws
