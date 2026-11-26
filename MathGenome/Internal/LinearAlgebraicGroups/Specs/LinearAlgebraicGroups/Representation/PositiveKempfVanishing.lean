import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Representation.FlagCohomology
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Representation.InducedNonvanishing

open CategoryTheory CategoryTheory.Limits

universe u

namespace LinearAlgebraicGroups.Specs.PositiveKempfVanishing

open CharacterDescent (Character)
open FlagCohomology (FlagKernelPair flagCohomology)
open FlagLineBundle (BorelProjection OppositeBorelPair)
open QuotientEmbedding (Presentation)
open InducedNonvanishing (Dominant)

/-- Positive-characteristic Kempf vanishing for the associated character
line on the quotient by the negative Borel. Dominance refers to the
simple coroots of the positive Borel in the same split pair. -/
def Statement : Prop :=
  ∀ {k : Type u} [Field k] (p : ℕ) [Fact p.Prime] [CharP k p]
    {G : AffineAlgebraicGroup k} (P : OppositeBorelPair G)
    (χ : Character P.torus.group), Dominant P χ →
    ∀ (Q : Presentation P.negative) (b : BorelProjection P)
      (h : FlagKernelPair Q) (i : ℕ), 0 < i →
      IsZero (flagCohomology Q b χ h i)

end LinearAlgebraicGroups.Specs.PositiveKempfVanishing
