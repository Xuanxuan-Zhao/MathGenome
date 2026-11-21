import MathGenome.Internal.Specs.D07.Ch06.SylowDefinition

/-!
Independent statements for `K07.06.sylow_conjugacy`, paper.tex:1040–1047.
Conjugacy is equality with the explicit image under `x ↦ g * x * g⁻¹`.
Both descriptions of Sylow subgroups established in the preceding entry
are included: largest prime-power order and maximality among p-subgroups.
Finiteness and primality remain hypotheses; exponent zero is allowed.
-/

namespace Specs.D07.Ch06.SylowConjugacy

universe u

/-- Sylow subgroups specified by their cardinalities are conjugate. -/
def ConjugateOfCard : Prop :=
  ∀ (G : Type u) [Group G] [Finite G] (p a m : ℕ),
    p.Prime → Nat.card G = p ^ a * m → ¬ p ∣ m →
    ∀ (P Q : Subgroup G), Nat.card P = p ^ a → Nat.card Q = p ^ a →
      ∃ g : G, (P : Set G) = (fun x : G => g * x * g⁻¹) '' (Q : Set G)

/-- All maximal finite p-subgroups are conjugate, without requiring the
caller to supply a factorization of the group order. -/
def ConjugateOfMaximal : Prop :=
  ∀ (G : Type u) [Group G] [Finite G] (p : ℕ), p.Prime →
    ∀ (P Q : Subgroup G),
      SylowDefinition.maximalPSubgroup p P → SylowDefinition.maximalPSubgroup p Q →
      ∃ g : G, (P : Set G) = (fun x : G => g * x * g⁻¹) '' (Q : Set G)

end Specs.D07.Ch06.SylowConjugacy
