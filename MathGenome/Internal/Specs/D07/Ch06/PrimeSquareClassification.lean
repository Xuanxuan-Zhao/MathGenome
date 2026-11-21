import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.Group.TypeTags.Basic
import Mathlib.Algebra.Group.Equiv.Defs
import Mathlib.SetTheory.Cardinal.Finite

/-!
Independent statements for K07.06.prime_square_classification
(paper.tex:998–1005; chapters/M07.06.tex:49–56).

The standard cyclic model Cₙ is the additive residue group ZMod n,
written multiplicatively. The product has its coordinatewise group law.
The disjunction records exactly one isomorphism type, with no extra
commutativity or exponent assumption on the input group.
-/

namespace Specs.D07.Ch06.PrimeSquareClassification

universe u

/-- The two proposed models are not isomorphic for any prime p. -/
def ModelsNonisomorphic : Prop :=
  ∀ (p : ℕ), p.Prime →
    ¬ Nonempty (Multiplicative (ZMod (p ^ 2)) ≃*
      (Multiplicative (ZMod p) × Multiplicative (ZMod p)))

/-- Every finite group of prime-square order has exactly one of the two types. -/
def Classification : Prop :=
  ∀ (G : Type u) [Group G] [Finite G] (p : ℕ), p.Prime →
    Nat.card G = p ^ 2 →
      (Nonempty (G ≃* Multiplicative (ZMod (p ^ 2))) ∧
        ¬ Nonempty (G ≃* (Multiplicative (ZMod p) × Multiplicative (ZMod p)))) ∨
      (Nonempty (G ≃* (Multiplicative (ZMod p) × Multiplicative (ZMod p))) ∧
        ¬ Nonempty (G ≃* Multiplicative (ZMod (p ^ 2))))

end Specs.D07.Ch06.PrimeSquareClassification
