import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Representation.PositiveKempfVanishing

open CategoryTheory CategoryTheory.Limits

universe u

namespace LinearAlgebraicGroups.Specs.KempfVanishing

open CharacterDescent (Character)
open FlagCohomology (FlagKernelPair flagCohomology)
open FlagLineBundle (BorelProjection OppositeBorelPair)
open QuotientEmbedding (Presentation)
open InducedNonvanishing (Dominant)

/-- Kempf vanishing over an arbitrary field for the line associated to a
dominant character of the split maximal torus, on the opposite flag. -/
def Statement : Prop :=
  ∀ {k : Type u} [Field k] {G : AffineAlgebraicGroup k}
    (P : OppositeBorelPair G) (χ : Character P.torus.group), Dominant P χ →
    ∀ (Q : Presentation P.negative) (b : BorelProjection P)
      (h : FlagKernelPair Q) (i : ℕ), 0 < i →
      IsZero (flagCohomology Q b χ h i)

end LinearAlgebraicGroups.Specs.KempfVanishing
