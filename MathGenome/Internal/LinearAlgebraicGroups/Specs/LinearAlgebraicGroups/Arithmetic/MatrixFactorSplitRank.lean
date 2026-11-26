import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Descent.RelativeRank
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Descent.AutomorphismSequence
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Reductive.GeneralLinearStructure

open CategoryTheory CategoryTheory.Limits

universe u

namespace LinearAlgebraicGroups.Specs.MatrixFactorSplitRank

open GeometricRadicals (IsReductive)
open RelativeRank (relativeRank)
open AutomorphismSequence (IsSeparableForm)
open GeneralLinearStructure (SpecialMatrixPoints)

/-- Ranks of the factors of a reductive product are finite and add in the product. -/
def ProductSplitRank : Prop :=
  ∀ {F : Type u} [Field F] (H H₁ H₂ : AffineAlgebraicGroup F),
    IsReductive H → IsReductive H₁ → IsReductive H₂ →
    (H.val ≅ Limits.prod H₁.val H₂.val) →
    ∃ r₁ r₂ : ℕ, relativeRank H₁ = (r₁ : WithBot ℕ∞) ∧
      relativeRank H₂ = (r₂ : WithBot ℕ∞) ∧
      relativeRank H = (r₁ : WithBot ℕ∞) + (r₂ : WithBot ℕ∞)

/-- An isotropic separable form of the size-two special linear group has
the special linear point model over the ground field. -/
def RankOneFormSplitRank : Prop :=
  ∀ {F : Type u} [Field F] (S U : AffineAlgebraicGroup F),
    SpecialMatrixPoints S 2 → IsReductive U → IsSeparableForm S U →
    relativeRank U = 0 ∨ (relativeRank U = 1 ∧ Nonempty (SpecialMatrixPoints U 2))

end LinearAlgebraicGroups.Specs.MatrixFactorSplitRank
