import MathGenome.Internal.Specs.D07.Ch14.FixedField

/-!
Independent specification of K07.14.normal_quotient, paper.tex:4190–4203.

The given algebra structure specifies the embedding K → L. The fixed field
uses the shared pointwise fixed-element definition, and H ranges over all
subgroups of the full K-automorphism group. Finite degree and the Galois
hypothesis on L/K are separate. No normality assumption is imposed in the
equivalence. In the quotient assertion normality is precisely its hypothesis.
The representative formula specifies the isomorphism induced by restriction,
including its values under the canonical inclusion of the fixed field in L.
-/

universe u v

namespace Specs.D07.Ch14.NormalQuotient

def GaloisIffNormal : Prop :=
  ∀ (K : Type u) (L : Type v) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L] (H : Subgroup (L ≃ₐ[K] L)),
    IsGalois K (FixedField.fixedFieldValue K L H) ↔ H.Normal

/-- A multiplicative equivalence whose value on σH is σ restricted to L^H. -/
def QuotientRestriction : Prop :=
  ∀ (K : Type u) (L : Type v) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    (H : Subgroup (L ≃ₐ[K] L)) [H.Normal],
    let E := FixedField.fixedFieldValue K L H
    ∃ e : (L ≃ₐ[K] L) ⧸ H ≃* (E ≃ₐ[K] E),
      ∀ (σ : L ≃ₐ[K] L) (x : E),
        algebraMap E L (e (QuotientGroup.mk' H σ) x) = σ (algebraMap E L x)

end Specs.D07.Ch14.NormalQuotient
