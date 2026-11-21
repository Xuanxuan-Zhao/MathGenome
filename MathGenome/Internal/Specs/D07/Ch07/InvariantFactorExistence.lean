import MathGenome.Internal.Specs.D07.Ch07.ClassificationDataConversion

/-! Independent statements of K07.07.invariant_factor_existence,
`paper.tex:3461–3470`. The cyclic group C_n is the additive group `ZMod n`.
The actual list is ordered by increasing divisibility and excludes C_1.
-/
namespace Specs.D07.Ch07.InvariantFactorExistence

universe u
open D07.Ch07.ClassificationDataConversion

/-- Every finite abelian group has normalized invariant factors. -/
def Existence : Prop :=
  ∀ (A : Type u) [AddCommGroup A] [Finite A],
    ∃ d : List ℕ, IsInvariant d ∧ Nonempty (A ≃+ InvariantGroup d)

/-- For the zero group the list can be empty (so its length is zero). -/
def ZeroGroupEmptyFactors : Prop :=
  ∀ (A : Type u) [AddCommGroup A] [Subsingleton A],
    IsInvariant [] ∧ Nonempty (A ≃+ InvariantGroup [])

end Specs.D07.Ch07.InvariantFactorExistence
