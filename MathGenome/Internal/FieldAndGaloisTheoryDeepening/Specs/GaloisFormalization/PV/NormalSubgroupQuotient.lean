import MathGenome.Internal.FieldAndGaloisTheoryDeepening.Specs.GaloisFormalization.PV.IntermediateFixedRing
import Mathlib.GroupTheory.QuotientGroup.Defs

namespace GaloisFormalization.PV.Specs

open scoped Matrix MatrixGroupCoordinates.Specs
open Matrix (GeneralLinearGroup)
open MatrixGroupCoordinates.Specs (IsRegularRepresentation)

universe u v w

/-- A closed subgroup is normal precisely when every member of the matrix
Galois group preserves its fixed subalgebra. -/
def fixedSubalgebraStableIffNormal : Prop :=
  ∀ {kind : OperatorKind} {K : Type u} {R : Type v}
    [Field K] [CommRing R] [Algebra K R] {n : ℕ}
    (δ : operatorField kind K) (A : linearSystem kind K n) (E : operator kind R)
    (T : operator kind (totalQuotientRing R)) (Y : GL (Fin n) R),
    isBaseField δ → isPicardVessiotTotalExtension δ A E T → isFundamental A E Y →
    let G := matrixGaloisGroup δ E Y
    ∀ (H : Subgroup G), IsClosed (H : Set G) →
      let F := matrixFixedSubalgebra δ E Y (H : Set G)
      (∀ (g : G) (x : F),
        matrixFractionAutomorphism δ E Y g (x : totalQuotientRing R) ∈ F) ↔ H.Normal

/-- Restriction to the fixed ring of a closed normal subgroup is regular
in the matrix realizations and induces the quotient isomorphism on points.
The target realization comes from a Picard–Vessiot ring embedded in the fixed ring. -/
def normalSubgroupQuotient : Prop :=
  ∀ {kind : OperatorKind} {K : Type u} {R : Type v}
    [Field K] [CommRing R] [Algebra K R] {n : ℕ}
    (δ : operatorField kind K) (A : linearSystem kind K n) (E : operator kind R)
    (T : operator kind (totalQuotientRing R)) (Y : GL (Fin n) R),
    isBaseField δ → isPicardVessiotTotalExtension δ A E T → isFundamental A E Y →
    let Q := totalQuotientRing R
    let G := matrixGaloisGroup δ E Y
    ∀ (H : Subgroup G), IsClosed (H : Set G) → ∀ (hH : H.Normal),
      letI : H.Normal := hH
      let F := matrixFixedSubalgebra δ E Y (H : Set G)
      ∃ (m : ℕ) (A' : linearSystem kind K m) (B : Subalgebra K Q)
        (D : operator kind B) (U : operator kind (totalQuotientRing B))
        (X : GL (Fin m) B) (EF : operator kind F)
        (j : totalQuotientRing B ≃ₐ[K] F),
        isPicardVessiotTotalExtension δ A' D U ∧ isFundamental A' D X ∧
        matrixGeneratedSubalgebra K X = ⊤ ∧ isAlgebra EF T ∧ commutes U EF j ∧
        (∀ b : B, (j (algebraMap B (totalQuotientRing B) b) : Q) = (b : Q)) ∧
        let G' := matrixGaloisGroup δ D X
        ∃ (e : G ⧸ H ≃* operatorAutomorphisms K EF)
          (φ : G' ≃* operatorAutomorphisms K EF),
          (∀ (g : G) (x : F),
            ((e (QuotientGroup.mk' H g)).val x : Q) =
              matrixFractionAutomorphism δ E Y g (x : Q)) ∧
          (∀ (g : G') (z : totalQuotientRing B),
            (φ g).val (j z) = j (matrixFractionAutomorphism δ D X g z)) ∧
          IsRegularRepresentation (G'.subtype.comp
            (φ.symm.toMonoidHom.comp (e.toMonoidHom.comp (QuotientGroup.mk' H))))

/-- An intermediate total ring given as an embedded Picard–Vessiot total
extension over the same base is preserved by the ambient Galois group. -/
def picardVessiotTotalSubextensionStable : Prop :=
  ∀ {kind : OperatorKind} {K : Type u} {R : Type v}
    [Field K] [CommRing R] [Algebra K R] {n : ℕ}
    (δ : operatorField kind K) (A : linearSystem kind K n) (E : operator kind R)
    (T : operator kind (totalQuotientRing R)) (Y : GL (Fin n) R),
    isBaseField δ → isPicardVessiotTotalExtension δ A E T → isFundamental A E Y →
    let Q := totalQuotientRing R
    ∀ (F : Subalgebra K Q), isIntermediateTotalRing T F →
      ∀ {B : Type w} [CommRing B] [Algebra K B] {m : ℕ}
        (A' : linearSystem kind K m) (D : operator kind B)
        (U : operator kind (totalQuotientRing B))
        (j : totalQuotientRing B →ₐ[K] Q),
        isPicardVessiotTotalExtension δ A' D U → Function.Injective j →
        commutes U T j → j.range = F →
        ∀ (g : matrixGaloisGroup δ E Y) (x : F),
          matrixFractionAutomorphism δ E Y g (x : Q) ∈ F

end GaloisFormalization.PV.Specs
