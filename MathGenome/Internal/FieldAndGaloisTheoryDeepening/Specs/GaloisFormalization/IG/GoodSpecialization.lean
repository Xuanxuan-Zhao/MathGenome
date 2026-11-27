import MathGenome.Internal.FieldAndGaloisTheoryDeepening.Specs.GaloisFormalization.IG.SpecializationDecomposition

open scoped Polynomial

namespace Specs.GaloisFormalization.IG

open SpecializationData SpecializationDecomposition

universe uk uℓ uL

/-- Good specialization identifies the fibre Galois group with the decomposition
subgroup at a point embedding. The residue isomorphism is induced by constant
coefficient on the valuation ring. -/
def GoodSpecialization : Prop :=
  ∀ {k : Type uk} [Field k] (ℓ : Type uℓ) [Field ℓ] [Algebra k ℓ]
    (a : k) (f : (RatFunc k)[X]) (hf : PolynomialRegularAt a f)
    (L : Type uL) [Field L] [Algebra (RatFunc k) L]
    [Polynomial.IsSplittingField (RatFunc k) L f]
    [Polynomial.IsSplittingField k ℓ (specialize a f hf)],
    f.Monic → (specialize a f hf).Separable →
    ∃ i : PointEmbedding (ℓ := ℓ) a L,
      MatchesRoots i f hf ∧
      inducedOrder i.toRingHom (algebraMap (RatFunc k) L (RatFunc.X - RatFunc.C a)) = 1 ∧
      Set.range (fun x : Lˣ => inducedOrder i.toRingHom (x : L)) =
        Set.range (fun n : ℤ => (n : WithTop ℤ)) ∧
      (letI := residueAlgebra i
       ∃ e : residueField i.toRingHom ≃ₐ[k] ℓ, e.toRingHom = residueEmbedding i.toRingHom) ∧
      ∃ d : decompositionGroup i ≃* (ℓ ≃ₐ[k] ℓ),
        (∀ (σ : decompositionGroup i) (x : valuationRing i.toRingHom),
          d σ (reduction i.toRingHom x) = reduction i.toRingHom (onValuationRing i σ x)) ∧
        d.toMonoidHom.ker = ⊥ ∧
        let embed := (decompositionGroup i).subtype.comp d.symm.toMonoidHom
        Function.Injective embed ∧ embed.range = decompositionGroup i

/-- Changing the point embedding amounts to precomposing with a generic Galois
automorphism, which conjugates the corresponding decomposition subgroups. -/
def GoodSpecializationConjugacy : Prop :=
  ∀ {k : Type uk} [Field k] (ℓ : Type uℓ) [Field ℓ] [Algebra k ℓ]
    (a : k) (f : (RatFunc k)[X]) (hf : PolynomialRegularAt a f)
    (L : Type uL) [Field L] [Algebra (RatFunc k) L]
    [Polynomial.IsSplittingField (RatFunc k) L f]
    [Polynomial.IsSplittingField k ℓ (specialize a f hf)],
    f.Monic → (specialize a f hf).Separable →
    ∀ i j : PointEmbedding (ℓ := ℓ) a L,
      ∃ σ : L ≃ₐ[RatFunc k] L,
        (∀ x : L, j x = i (σ x)) ∧
        (decompositionGroup j).map (MulAut.conj σ).toMonoidHom = decompositionGroup i

end Specs.GaloisFormalization.IG
