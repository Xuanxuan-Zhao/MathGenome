import MathGenome.Internal.Specs.D07.Ch07.ClassificationDataConversion

/-!
Independent statement of K07.07.invariant_factor_uniqueness,
paper.tex:3469–3476. The shared `IsInvariant` predicate says that all
entries are at least two and the list is increasing in divisibility.
`InvariantGroup` is the finite Cartesian product of the additive groups
`ZMod dᵢ`, including the empty product. Equality of lists states both
equality of lengths and equality of all corresponding entries.
-/
namespace Specs.D07.Ch07.InvariantFactorUniqueness

open D07.Ch07.ClassificationDataConversion

def Uniqueness : Prop :=
  ∀ (d e : List ℕ), IsInvariant d → IsInvariant e →
    (InvariantGroup d ≃+ InvariantGroup e) → d = e

end Specs.D07.Ch07.InvariantFactorUniqueness
