import MathGenome.Internal.FieldAndGaloisTheoryDeepening.Specs.GaloisFormalization.IG.SpecializationDecomposition
import MathGenome.Internal.FieldAndGaloisTheoryDeepening.Specs.GaloisFormalization.IG.SpecializationCoefficients
import Mathlib.FieldTheory.Normal.Basic

open scoped Polynomial

namespace Specs.GaloisFormalization.IG.TowerSpecialization

open SpecializationData SpecializationCoefficients SpecializationDecomposition

noncomputable section

universe uk uℓ uL

variable {k : Type uk} [Field k] {ℓ : Type uℓ} [Field ℓ] [Algebra k ℓ]
  {a : k} {L : Type uL} [Field L] [Algebra (RatFunc k) L]

/-- Inclusion of the valuation ring of the restricted valuation. -/
def includeValuationRing (i : PointEmbedding (ℓ := ℓ) a L)
    (L₀ : IntermediateField (RatFunc k) L) (E : IntermediateField k ℓ)
    (j : PointEmbedding (ℓ := E) a L₀)
    (hw : ∀ x : L₀, inducedOrder j.toRingHom x = inducedOrder i.toRingHom (x : L)) :
    valuationRing j.toRingHom →+* valuationRing i.toRingHom :=
  (L₀.val.toRingHom.comp (valuationRing j.toRingHom).subtype).codRestrict _ fun x => by
    change 0 ≤ inducedOrder i.toRingHom ((x : L₀) : L)
    rw [← hw]
    exact x.property

/-- Actual restriction of the stabilizer of the valuation to the intermediate field. -/
def restrictDecomposition (i : PointEmbedding (ℓ := ℓ) a L)
    (L₀ : IntermediateField (RatFunc k) L) [Normal (RatFunc k) L₀]
    (E : IntermediateField k ℓ) (j : PointEmbedding (ℓ := E) a L₀)
    (hw : ∀ x : L₀, inducedOrder j.toRingHom x = inducedOrder i.toRingHom (x : L)) :
    decompositionGroup i →* decompositionGroup j :=
  ((AlgEquiv.restrictNormalHom L₀).comp (decompositionGroup i).subtype).codRestrict _ fun σ => by
    intro x hx
    change inducedOrder j.toRingHom (AlgEquiv.restrictNormalHom L₀ σ.val x) =
      inducedOrder j.toRingHom x
    rw [hw, AlgEquiv.restrictNormalHom_apply, hw x]
    exact σ.property (x : L) (fun h => hx (Subtype.ext h))

/-- In a tower at a good point, the lower residue field is the fibre splitting
field inside the upper residue field, and the reduction isomorphisms intertwine
restriction. The lower order is the restriction of the given upper order. -/
abbrev TowerSpecializationType : Prop :=
  ∀ {k : Type uk} [Field k] {ℓ : Type uℓ} [Field ℓ] [Algebra k ℓ]
    {a : k} {L : Type uL} [Field L] [Algebra (RatFunc k) L]
    (f f₀ : (RatFunc k)[X]) (hf : PolynomialRegularAt a f) (hf₀ : PolynomialRegularAt a f₀),
    f.Monic → f₀.Monic → (specialize a f hf).Separable → (specialize a f₀ hf₀).Separable →
    ∀ [Polynomial.IsSplittingField (RatFunc k) L f]
      [Polynomial.IsSplittingField k ℓ (specialize a f hf)]
      (i : PointEmbedding (ℓ := ℓ) a L), MatchesRoots i f hf →
    ∀ (L₀ : IntermediateField (RatFunc k) L) [Polynomial.IsSplittingField (RatFunc k) L₀ f₀],
    let E := IntermediateField.adjoin k ((specialize a f₀ hf₀).rootSet ℓ)
    ∃ hE : Polynomial.IsSplittingField k E (specialize a f₀ hf₀),
    letI := hE
    letI := Normal.of_isSplittingField (E := E) (specialize a f₀ hf₀)
    letI := Normal.of_isSplittingField (E := L₀) f₀
    letI := Normal.of_isSplittingField (E := ℓ) (specialize a f hf)
    ∃ j : PointEmbedding (ℓ := E) a L₀, MatchesRoots j f₀ hf₀ ∧
      (∀ x : L₀, laurentMap (algebraMap E ℓ) (j x) = i (x : L)) ∧
    ∃ hw : ∀ x : L₀, inducedOrder j.toRingHom x = inducedOrder i.toRingHom (x : L),
    letI := residueAlgebra i
    letI := residueAlgebra j
    ∃ (e : residueField i.toRingHom ≃ₐ[k] ℓ) (e₀ : residueField j.toRingHom ≃ₐ[k] E)
      (d : decompositionGroup i ≃* (ℓ ≃ₐ[k] ℓ))
      (d₀ : decompositionGroup j ≃* (E ≃ₐ[k] E)),
      e.toRingHom = residueEmbedding i.toRingHom ∧
      e₀.toRingHom = residueEmbedding j.toRingHom ∧
      (∀ x : valuationRing j.toRingHom,
        (e₀ (IsLocalRing.residue _ x) : ℓ) =
          e (IsLocalRing.residue _ (includeValuationRing i L₀ E j hw x))) ∧
      (∀ (σ : decompositionGroup i) (x : valuationRing i.toRingHom),
        d σ (reduction i.toRingHom x) = reduction i.toRingHom (onValuationRing i σ x)) ∧
      (∀ (σ : decompositionGroup j) (x : valuationRing j.toRingHom),
        d₀ σ (reduction j.toRingHom x) = reduction j.toRingHom (onValuationRing j σ x)) ∧
      (∀ σ : decompositionGroup i,
        d₀ (restrictDecomposition i L₀ E j hw σ) = AlgEquiv.restrictNormalHom E (d σ)) ∧
      Function.Surjective (AlgEquiv.restrictNormalHom E : (ℓ ≃ₐ[k] ℓ) →* (E ≃ₐ[k] E)) ∧
      Function.Surjective (restrictDecomposition i L₀ E j hw)

end

end Specs.GaloisFormalization.IG.TowerSpecialization
