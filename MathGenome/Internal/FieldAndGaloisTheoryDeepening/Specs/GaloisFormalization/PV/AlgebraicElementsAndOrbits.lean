import MathGenome.Internal.FieldAndGaloisTheoryDeepening.Specs.GaloisFormalization.PV.IntermediateFixedRing
import MathGenome.Internal.FieldAndGaloisTheoryDeepening.Specs.GaloisFormalization.PV.MatrixGroupIdentityComponent
import Mathlib.FieldTheory.AlgebraicClosure

namespace GaloisFormalization.PV.Specs

open scoped Matrix MatrixGroupCoordinates.Specs
open MatrixGroupIdentityComponent.Specs (identityComponent)

/-- In a differential Picard–Vessiot extension, the identity-component invariants
form the relative algebraic closure of the base field in the total quotient field.
The corresponding minimal polynomials split there and have degree at most the
index of the identity component. -/
def algebraicElementsAndOrbits.{u, v} : Prop :=
  ∀ {K : Type u} {R : Type v} [Field K] [CommRing R] [Algebra K R] {n : ℕ}
    (δ : operatorField .differential K) (A : linearSystem .differential K n)
    (E : operator .differential R) (T : operator .differential (totalQuotientRing R))
    (Y : GL (Fin n) R),
    isBaseField δ → isPicardVessiotTotalExtension δ A E T → isFundamental A E Y →
    let Q := totalQuotientRing R
    let G := matrixGaloisGroup δ E Y
    let H := identityComponent G
    let F := matrixFixedSubalgebra δ E Y (H : Set G)
    ∃ hQ : IsField Q,
      letI : Field Q := hQ.toField
      F = (algebraicClosure K Q).toSubalgebra ∧
      ∀ x : F,
        (minpoly K (x : Q)).natDegree ≤ H.index ∧
        ((minpoly K (x : Q)).map (algebraMap K F)).Splits

end GaloisFormalization.PV.Specs
