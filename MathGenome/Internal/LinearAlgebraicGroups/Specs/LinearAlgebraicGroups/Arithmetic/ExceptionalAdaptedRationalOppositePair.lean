import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Arithmetic.QuasiSplitPinnedPairModel

universe u

namespace LinearAlgebraicGroups.Specs.ExceptionalAdaptedRationalOppositePair

open GeometricBorelConjugacy (IsKBorel)
open GeometricRadicals (IsReductive IsTorus)
open QuasiSplitPinnedPairModel (BorelPair)
open RankOneFlag (IsGeometricallyMaximal)
open SchemeDerivedGroup (IsSubgroupOf)

/-- A rational Borel and a geometrically maximal torus of the ambient reductive
group contained in it extend to an opposite Borel pair over the ground field.
The pair records the scheme-theoretic intersection and the unipotent radicals
of both Borels. -/
def Statement : Prop :=
  ∀ {F : Type u} [Field F] (G : AffineAlgebraicGroup F), IsReductive G →
    ∀ (J T : ClosedSubgroup G.val), IsKBorel J → IsTorus T.group →
      IsGeometricallyMaximal T → IsSubgroupOf T J →
      ∃ P : BorelPair G, P.positive = J ∧ P.torus = T

end LinearAlgebraicGroups.Specs.ExceptionalAdaptedRationalOppositePair
