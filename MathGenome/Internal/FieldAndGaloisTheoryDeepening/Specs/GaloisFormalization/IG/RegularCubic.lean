import MathGenome.Internal.FieldAndGaloisTheoryDeepening.Specs.GaloisFormalization.IG.CubicGaloisCriterion
import MathGenome.Internal.FieldAndGaloisTheoryDeepening.Specs.GaloisFormalization.IG.GenericCubic
import MathGenome.Internal.FieldAndGaloisTheoryDeepening.Specs.GaloisFormalization.IG.GeometricGaloisGroup
import MathGenome.Internal.FieldAndGaloisTheoryDeepening.Specs.GaloisFormalization.IG.GoodSpecialization
import MathGenome.Internal.FieldAndGaloisTheoryDeepening.Specs.GaloisFormalization.IG.OddCubicFibres

open Polynomial

namespace GaloisFormalization.IG.RegularCubicSpec

open Specs.GaloisFormalization.IG.SpecializationData
  Specs.GaloisFormalization.IG.SpecializationDecomposition

universe u v

/-- The actual generic cubic is regular at every rational parameter. -/
def CoefficientsRegular : Prop :=
  ∀ a : ℚ,
    PolynomialRegularAt a
      (Specs.GaloisFormalization.IG.GenericCubic.polynomial (RatFunc.X : RatFunc ℚ))

/-- The specialization in the regular coefficient subring gives the stated integer fibre. -/
def SpecializationFormula : Prop :=
  ∀ (a : ℤ) (hf : PolynomialRegularAt (a : ℚ)
      (Specs.GaloisFormalization.IG.GenericCubic.polynomial (RatFunc.X : RatFunc ℚ))),
    specialize (a : ℚ) _ hf = OddCubicFibresSpec.polynomial a

/-- Each splitting field of the generic cubic is finite Galois and regular over
the rational constants, with the full permutation action on its three roots. -/
def RegularGenericCubic : Prop :=
  ∀ (L : Type u) [Field L] [Algebra (RatFunc ℚ) L],
    let f := Specs.GaloisFormalization.IG.GenericCubic.polynomial (RatFunc.X : RatFunc ℚ)
    ∀ [f.IsSplittingField (RatFunc ℚ) L],
      letI : Algebra ℚ L := Algebra.compHom L (algebraMap ℚ (RatFunc ℚ))
      FiniteDimensional (RatFunc ℚ) L ∧ IsGalois (RatFunc ℚ) L ∧ Specs.isRegularOver ℚ L ∧
        ∃ (e : CubicRootOrdering f L)
          (φ : (L ≃ₐ[RatFunc ℚ] L) ≃* Equiv.Perm (Fin 3)),
          φ.toMonoidHom = cubicRootAction e

/-- Every odd integer is a good point, with full symmetric group on the
specialized roots. Reduction identifies it with the entire generic group. -/
def OddSpecialization : Prop :=
  ∀ (L : Type u) [Field L] [Algebra (RatFunc ℚ) L],
    let f := Specs.GaloisFormalization.IG.GenericCubic.polynomial (RatFunc.X : RatFunc ℚ)
    ∀ [f.IsSplittingField (RatFunc ℚ) L] (a : ℤ), Odd a →
      ∃ hf : PolynomialRegularAt (a : ℚ) f,
      let g := specialize (a : ℚ) f hf
      f.Monic ∧ g.Separable ∧
        ∀ (ℓ : Type v) [Field ℓ] [Algebra ℚ ℓ] [g.IsSplittingField ℚ ℓ],
          (∃ (e : CubicRootOrdering g ℓ) (φ : (ℓ ≃ₐ[ℚ] ℓ) ≃* Equiv.Perm (Fin 3)),
            φ.toMonoidHom = cubicRootAction e) ∧
          (∃ i : PointEmbedding (ℓ := ℓ) (a : ℚ) L,
            MatchesRoots i f hf ∧ decompositionGroup i = ⊤ ∧
              ∃ d : decompositionGroup i ≃* (ℓ ≃ₐ[ℚ] ℓ),
                ∀ (σ : decompositionGroup i) (x : valuationRing i.toRingHom),
                  d σ (reduction i.toRingHom x) =
                    reduction i.toRingHom (onValuationRing i σ x)) ∧
          ∀ i : PointEmbedding (ℓ := ℓ) (a : ℚ) L,
            MatchesRoots i f hf → decompositionGroup i = ⊤

end GaloisFormalization.IG.RegularCubicSpec
