import MathGenome.Internal.Specs.D07.Ch01.HomomorphismDefinition
import MathGenome.Internal.Specs.D07.Ch01.IntegerPowerLaws

/-!
Independent specification of `K07.01.hom_preserves_powers`
(paper.tex:303–310, chapters/M07.01.tex:88–95).

The groups are arbitrary, and may have different universe levels. The
homomorphism is the same canonical bundled map as in the upstream Specs.
Division is the group operation `x / y = x * y⁻¹`; integer powers use the
canonical operation identified with the source conventions upstream.
There are no finiteness, commutativity, or nontriviality assumptions.
-/

namespace Specs.D07.Ch01.HomPreservesPowers

universe u v

/-- Every group homomorphism preserves division, in the source's order. -/
def PreservesDivision : Prop :=
  ∀ (G : Type u) (H : Type v) [Group G] [Group H]
    (f : G →* H) (x y : G), f (x / y) = f x / f y

/-- Every group homomorphism preserves powers for all integer exponents. -/
def PreservesIntegerPowers : Prop :=
  ∀ (G : Type u) (H : Type v) [Group G] [Group H]
    (f : G →* H) (x : G) (n : ℤ), f (x ^ n) = f x ^ n

end Specs.D07.Ch01.HomPreservesPowers
