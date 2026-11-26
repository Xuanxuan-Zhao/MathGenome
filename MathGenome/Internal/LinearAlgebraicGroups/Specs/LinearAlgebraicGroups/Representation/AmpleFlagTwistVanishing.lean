import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Representation.AmpleFlagWeights
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Representation.FlagCohomology

open CategoryTheory

universe u

namespace LinearAlgebraicGroups.Specs.AmpleFlagTwistVanishing

open AmpleFlagWeights (IsAmple)
open CharacterDescent (Character)
open FlagCohomology (FlagKernelPair flagCohomology)
open FlagLineBundle (BorelProjection OppositeBorelPair)
open QuotientEmbedding (Presentation)

/-- Every fixed flag character sheaf has vanishing higher cohomology after
sufficiently many twists by an ample flag character sheaf. -/
def EventualVanishing : Prop :=
  ∀ {k : Type u} [Field k] {G : AffineAlgebraicGroup k} (P : OppositeBorelPair G)
    (Q : Presentation P.negative) (b : BorelProjection P) (h : FlagKernelPair Q)
    (θ χ : Character P.torus.group), IsAmple Q b θ →
    ∃ N : ℕ, ∀ t : ℕ, N ≤ t → ∀ i : ℕ, 0 < i →
      Limits.IsZero (flagCohomology Q b (χ * θ ^ t) h i)

end LinearAlgebraicGroups.Specs.AmpleFlagTwistVanishing
