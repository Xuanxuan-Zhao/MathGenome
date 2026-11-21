import MathGenome.Internal.Specs.D07.Ch14.NormalQuotientRestrictionSurjectivity

/-!
Independent specification of K07.14.restriction_exactness, paper.tex:4200–4209.

The compatible field embeddings are recorded by the three Algebra structures
and IsScalarTower. Galois and finite degree are separate hypotheses. The
inclusion retains the underlying automorphism of L; restriction is the shared
map specified in NormalQuotientRestrictionSurjectivity, whose value on E is
characterized there along its given embedding in L.

Injectivity, equality of image and kernel, and surjectivity express exactness
of 1 → Gal(L/E) → Gal(L/K) → Gal(E/K) → 1, including both endpoints.
No choice of an algebraic closure or literal inclusion of field types is needed.
-/

universe u v w

namespace Specs.D07.Ch14.RestrictionExactness

def InclusionHomType : Type (max u v w + 1) :=
  ∀ (K : Type u) (E : Type v) (L : Type w)
    [Field K] [Field E] [Field L]
    [Algebra K E] [Algebra K L] [Algebra E L] [IsScalarTower K E L],
    (L ≃ₐ[E] L) →* (L ≃ₐ[K] L)

def inclusionHomValue : InclusionHomType.{u, v, w} :=
  fun K _ _ _ _ _ _ _ _ _ => AlgEquiv.restrictScalarsHom K

/-- The first map is inclusion of the same field automorphisms. -/
def InclusionAgrees : Prop :=
  ∀ (K : Type u) (E : Type v) (L : Type w)
    [Field K] [Field E] [Field L]
    [Algebra K E] [Algebra K L] [Algebra E L] [IsScalarTower K E L]
    (σ : L ≃ₐ[E] L) (x : L), inclusionHomValue K E L σ x = σ x

/-- All three exactness conditions for the specified homomorphisms. -/
def RestrictionExactSequence : Prop :=
  ∀ (K : Type u) (E : Type v) (L : Type w)
    [Field K] [Field E] [Field L]
    [Algebra K E] [Algebra K L] [Algebra E L] [IsScalarTower K E L]
    [FiniteDimensional K L] [IsGalois K L] [IsGalois K E],
    let i := inclusionHomValue K E L
    let r := NormalQuotientRestrictionSurjectivity.restrictionHomValue K E L
    Function.Injective i ∧ i.range = r.ker ∧ Function.Surjective r

end Specs.D07.Ch14.RestrictionExactness
