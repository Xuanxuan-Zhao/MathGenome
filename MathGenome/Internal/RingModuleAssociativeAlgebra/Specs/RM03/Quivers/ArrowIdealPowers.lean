import MathGenome.Internal.RingModuleAssociativeAlgebra.Specs.RM03.Quivers.Relations

/-! The path-length description of powers of the arrow ideal. -/

universe u v w

namespace RM03.ArrowIdealPowersSpec

attribute [local instance] QuiverRelationSpec.nonUnitalNonAssocRing

/-- For `m ≥ 1`, the arrow ideal to the power `m` is the `k`-linear span of
the basis paths of length at least `m`. -/
def PowerEqualsSpan : Prop :=
  ∀ {k : Type w} {Q : Type u} [Field k] [Quiver.{v} Q] [Fintype Q]
    (m : ℕ), 1 ≤ m →
    (QuiverRelationSpec.idealPower (QuiverRelationSpec.arrowIdeal k Q) m :
        Set (PathAlgebraSpec.Carrier k Q)) =
      (Submodule.span k (PathAlgebraSpec.ofPath k Q '' {p : Path Q | m ≤ p.length}) :
        Set (PathAlgebraSpec.Carrier k Q))

end RM03.ArrowIdealPowersSpec
