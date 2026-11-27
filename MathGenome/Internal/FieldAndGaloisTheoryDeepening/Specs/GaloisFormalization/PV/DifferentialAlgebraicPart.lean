import MathGenome.Internal.FieldAndGaloisTheoryDeepening.Specs.GaloisFormalization.PV.AlgebraicElementsAndOrbits
import MathGenome.Internal.FieldAndGaloisTheoryDeepening.Specs.GaloisFormalization.PV.NormalSubgroupQuotient
import Mathlib.FieldTheory.Galois.Basic

namespace GaloisFormalization.PV.Specs

open scoped Matrix MatrixGroupCoordinates.Specs
open MatrixGroupIdentityComponent.Specs (identityComponent)

/-- The fixed field of the Zariski identity component is the relative algebraic
closure of the base in the differential Picard–Vessiot field. It is finite
Galois, and restriction induces the quotient isomorphism. -/
def differentialAlgebraicPart.{u, v} : Prop :=
  ∀ {K : Type u} {R : Type v} [Field K] [CommRing R] [Algebra K R] {n : ℕ}
    (δ : operatorField .differential K) (A : linearSystem .differential K n)
    (E : operator .differential R) (T : operator .differential (totalQuotientRing R))
    (Y : GL (Fin n) R),
    isBaseField δ → isPicardVessiotTotalExtension δ A E T → isFundamental A E Y →
    let Q := totalQuotientRing R
    let G := matrixGaloisGroup δ E Y
    let H := identityComponent G
    let F := matrixFixedSubalgebra δ E Y (H : Set G)
    ∃ (hQ : IsField Q) (hF : IsField F) (hH : H.Normal),
      letI : Field Q := hQ.toField
      letI : Field F := hF.toField
      letI : H.Normal := hH
      F = (algebraicClosure K Q).toSubalgebra ∧
      FiniteDimensional K F ∧ IsGalois K F ∧
      ∃ e : G ⧸ H ≃* (F ≃ₐ[K] F),
        ∀ (g : G) (x : F),
          (e (QuotientGroup.mk' H g) x : Q) = matrixFractionAutomorphism δ E Y g (x : Q)

end GaloisFormalization.PV.Specs
