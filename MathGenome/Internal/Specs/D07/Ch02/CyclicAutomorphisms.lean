import MathGenome.Internal.Specs.D07.Ch01.HomOnGenerators
import MathGenome.Internal.Specs.D07.Ch01.ArithmeticExamples
import MathGenome.Internal.Specs.D07.Ch02.FiniteCyclicSubgroupClassification
import MathGenome.Internal.Specs.D07.Ch02.SubgroupsOfIntegerGroup
import Mathlib.Algebra.Group.End

/-!
Independent specification of K07.02.cyclic_automorphisms (paper.tex:489–497).
`MulAut` is the group of automorphisms under rightmost-first composition.
Generation is by the canonical integer-power subgroup. Positive natural
cardinality expresses finite group order, including n = 1. Exponents are
integers, and gcd(a,n) is represented by Nat.gcd a.natAbs n.
The isomorphism statement identifies the residue unit with the exponent
on the *specified* generator, rather than merely asserting an abstract
isomorphism. The integer statement includes existence of both maps.
-/
namespace Specs.D07.Ch02.CyclicAutomorphisms

universe u v

/-- A homomorphism out of a cyclic group is determined by its generator. -/
def HomDeterminedByGenerator : Prop :=
  ∀ (G : Type u) (H : Type v) [Group G] [Group H] (x : G),
    Subgroup.zpowers x = ⊤ → ∀ f g : G →* H, f = g ↔ f x = g x

/-- The automorphism/unit correspondence records exactly the generator image. -/
def FiniteAutomorphismEquivalence : Prop :=
  ∀ (G : Type u) [Group G] (x : G) (n : ℕ),
    Subgroup.zpowers x = ⊤ → 0 < n → Nat.card G = n →
      ∃ E : MulAut G ≃* (ZMod n)ˣ,
        ∀ (f : MulAut G) (a : ℤ),
          (E f : ZMod n) = (a : ZMod n) ↔ f x = x ^ a

/-- Every automorphism has a relatively prime exponent, on every power of x. -/
def FiniteAutomorphismForm : Prop :=
  ∀ (G : Type u) [Group G] (x : G) (n : ℕ),
    Subgroup.zpowers x = ⊤ → 0 < n → Nat.card G = n →
      ∀ f : MulAut G, ∃ a : ℤ, Nat.gcd a.natAbs n = 1 ∧
        ∀ k : ℤ, f (x ^ k) = x ^ (a * k)

/-- Conversely each relatively prime exponent gives a unique automorphism. -/
def PowerAutomorphismIff : Prop :=
  ∀ (G : Type u) [Group G] (x : G) (n : ℕ),
    Subgroup.zpowers x = ⊤ → 0 < n → Nat.card G = n →
      ∀ a : ℤ, (∃! f : MulAut G, ∀ k : ℤ, f (x ^ k) = x ^ (a * k)) ↔
        Nat.gcd a.natAbs n = 1

/-- All endomorphisms of the additive integers are multiplication by f(1). -/
def IntegerEndomorphismForm : Prop :=
  ∀ (f : ℤ →+ ℤ) (k : ℤ), f k = f 1 * k

/-- There are precisely the identity and negation automorphisms of (ℤ,+). -/
def IntegerAutomorphisms : Prop :=
  ∃ epos eneg : ℤ ≃+ ℤ,
    (∀ k : ℤ, epos k = k) ∧ (∀ k : ℤ, eneg k = -k) ∧
      epos ≠ eneg ∧ ∀ f : ℤ ≃+ ℤ, f = epos ∨ f = eneg

end Specs.D07.Ch02.CyclicAutomorphisms
