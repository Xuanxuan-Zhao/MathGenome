import MathGenome.Internal.Specs.D07.Ch14.FixedField

/-!
Independent specification for the restriction-surjectivity part of
K07.14.normal_quotient (paper.tex:4190–4203).

The three fields have specified compatible embeddings. Normality of E/K
makes restriction an automorphism of E, rather than a map to a conjugate
field. Finite degree and the Galois hypothesis on L/K are stated separately
in the extension and surjectivity assertions. The kernel is described both
for an arbitrary scalar tower and for a literal intermediate field, using
the shared canonical fixing subgroup in the latter case.
-/

universe u v w

namespace Specs.D07.Ch14.NormalQuotientRestrictionSurjectivity

def RestrictionHomType : Type (max u v w + 1) :=
  ∀ (K : Type u) (E : Type v) (L : Type w)
    [Field K] [Field E] [Field L]
    [Algebra K E] [Algebra K L] [Algebra E L] [IsScalarTower K E L]
    [Normal K E], (L ≃ₐ[K] L) →* (E ≃ₐ[K] E)

noncomputable def restrictionHomValue : RestrictionHomType.{u, v, w} :=
  fun _ E _ _ _ _ _ _ _ _ _ => AlgEquiv.restrictNormalHom E

/-- This is restriction along the given embedding of E in L. -/
def RestrictionAgrees : Prop :=
  ∀ (K : Type u) (E : Type v) (L : Type w)
    [Field K] [Field E] [Field L]
    [Algebra K E] [Algebra K L] [Algebra E L] [IsScalarTower K E L]
    [Normal K E] (σ : L ≃ₐ[K] L) (x : E),
    algebraMap E L (restrictionHomValue K E L σ x) = σ (algebraMap E L x)

/-- Multiplication of automorphisms is left function composition. -/
def RestrictionGroupLaws : Prop :=
  ∀ (K : Type u) (E : Type v) (L : Type w)
    [Field K] [Field E] [Field L]
    [Algebra K E] [Algebra K L] [Algebra E L] [IsScalarTower K E L]
    [Normal K E],
    restrictionHomValue K E L 1 = 1 ∧
      ∀ σ τ : L ≃ₐ[K] L,
        restrictionHomValue K E L (σ * τ) =
          restrictionHomValue K E L σ * restrictionHomValue K E L τ

/-- Every prescribed K-automorphism of E extends with the specified values. -/
def AutomorphismExtension : Prop :=
  ∀ (K : Type u) (E : Type v) (L : Type w)
    [Field K] [Field E] [Field L]
    [Algebra K E] [Algebra K L] [Algebra E L] [IsScalarTower K E L]
    [FiniteDimensional K L] [IsGalois K L] [Normal K E]
    (τ : E ≃ₐ[K] E),
    ∃ σ : L ≃ₐ[K] L,
      ∀ x : E, σ (algebraMap E L x) = algebraMap E L (τ x)

def RestrictionSurjective : Prop :=
  ∀ (K : Type u) (E : Type v) (L : Type w)
    [Field K] [Field E] [Field L]
    [Algebra K E] [Algebra K L] [Algebra E L] [IsScalarTower K E L]
    [FiniteDimensional K L] [IsGalois K L] [Normal K E],
    Function.Surjective (restrictionHomValue K E L)

/-- For arbitrary embeddings, fix the actual image of E in L pointwise. -/
def RestrictionKernel : Prop :=
  ∀ (K : Type u) (E : Type v) (L : Type w)
    [Field K] [Field E] [Field L]
    [Algebra K E] [Algebra K L] [Algebra E L] [IsScalarTower K E L]
    [Normal K E],
    (restrictionHomValue K E L).ker =
      (IsScalarTower.toAlgHom K E L).fieldRange.fixingSubgroup

/-- In the shared intermediate-field representation this is exactly G_E. -/
def IntermediateRestrictionKernel : Prop :=
  ∀ (K : Type u) (L : Type v) [Field K] [Field L] [Algebra K L]
    (E : IntermediateField K L) [Normal K E],
    (restrictionHomValue K E L).ker = FixedField.fixingSubgroupValue K L E

end Specs.D07.Ch14.NormalQuotientRestrictionSurjectivity
