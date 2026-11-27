import MathGenome.Internal.FieldAndGaloisTheoryDeepening.Specs.GaloisFormalization.IG.SpecializationData
import Mathlib.FieldTheory.SplittingField.IsSplittingField
import Mathlib.FieldTheory.Separable

open scoped Polynomial

namespace Specs.GaloisFormalization.IG.SpecializationDecomposition

open SpecializationData

noncomputable section

universe uk uℓ uL

section Constructions

variable {k : Type uk} [Field k] {ℓ : Type uℓ} [Field ℓ] [Algebra k ℓ]
  {a : k} {L : Type uL} [Field L] [Algebra (RatFunc k) L]

/-- Constants from the base field as elements of the induced valuation ring. -/
def constantInValuationRing (i : PointEmbedding (ℓ := ℓ) a L) :
    k →+* valuationRing i.toRingHom :=
  ((algebraMap (RatFunc k) L).comp RatFunc.C).codRestrict _ fun c => by
    let := substitutionAlgebra ℓ a
    change 0 ≤ (i (algebraMap (RatFunc k) L (RatFunc.C c))).orderTop
    rw [AlgHom.commutes]
    change 0 ≤ (substitution ℓ a (RatFunc.C c)).orderTop
    rw [← RatFunc.algebraMap_eq_C, AlgHom.commutes]
    rw [HahnSeries.algebraMap_apply', PowerSeries.algebraMap_apply, HahnSeries.ofPowerSeries_C,
      HahnSeries.C_apply]
    simpa only [WithTop.coe_zero] using
      (HahnSeries.orderTop_single_le (a := (0 : ℤ)) (r := algebraMap k ℓ c))

/-- The base-field structure of the actual residue quotient, induced by the constants. -/
abbrev residueAlgebra (i : PointEmbedding (ℓ := ℓ) a L) : Algebra k (residueField i.toRingHom) :=
  ((IsLocalRing.residue (valuationRing i.toRingHom)).comp (constantInValuationRing i)).toAlgebra

/-- Restriction of a valuation-preserving automorphism to the valuation ring. -/
def onValuationRing (i : PointEmbedding (ℓ := ℓ) a L) (σ : decompositionGroup i) :
    valuationRing i.toRingHom →+* valuationRing i.toRingHom :=
  (((σ : L ≃ₐ[RatFunc k] L) : L →+* L).comp (valuationRing i.toRingHom).subtype).codRestrict _
    fun x => by
      change 0 ≤ inducedOrder i.toRingHom ((σ : L ≃ₐ[RatFunc k] L) x)
      by_cases hx : (x : L) = 0
      · rw [hx, map_zero, AddValuation.map_zero]
        exact le_top
      · rw [σ.property _ hx]
        exact x.property

end Constructions

set_option linter.checkUnivs false in
def ConstantInValuationRingType :=
  ∀ {k : Type uk} [Field k] {ℓ : Type uℓ} [Field ℓ] [Algebra k ℓ]
    {a : k} {L : Type uL} [Field L] [Algebra (RatFunc k) L]
    (i : PointEmbedding (ℓ := ℓ) a L),
    k →+* valuationRing i.toRingHom

set_option linter.checkUnivs false in
def ResidueAlgebraType :=
  ∀ {k : Type uk} [Field k] {ℓ : Type uℓ} [Field ℓ] [Algebra k ℓ]
    {a : k} {L : Type uL} [Field L] [Algebra (RatFunc k) L]
    (i : PointEmbedding (ℓ := ℓ) a L),
    Algebra k (residueField i.toRingHom)

set_option linter.checkUnivs false in
def OnValuationRingType :=
  ∀ {k : Type uk} [Field k] {ℓ : Type uℓ} [Field ℓ] [Algebra k ℓ]
    {a : k} {L : Type uL} [Field L] [Algebra (RatFunc k) L]
    (i : PointEmbedding (ℓ := ℓ) a L) (_σ : decompositionGroup i),
    valuationRing i.toRingHom →+* valuationRing i.toRingHom

/-- The order of the translated parameter is one, and the nonzero values are exactly ℤ. -/
abbrev NormalizedValueGroup : Prop :=
  ∀ {k : Type uk} [Field k] {ℓ : Type uℓ} [Field ℓ] [Algebra k ℓ]
    {a : k} {L : Type uL} [Field L] [Algebra (RatFunc k) L]
    (i : PointEmbedding (ℓ := ℓ) a L),
    inducedOrder i.toRingHom (algebraMap (RatFunc k) L (RatFunc.X - RatFunc.C a)) = 1 ∧
    Set.range (fun x : Lˣ => inducedOrder i.toRingHom (x : L)) =
      Set.range (fun n : ℤ => (n : WithTop ℤ))

/-- Constant coefficient identifies the actual residue quotient with the fibre splitting field. -/
abbrev ResidueFieldEquivalence : Prop :=
  ∀ {k : Type uk} [Field k] {ℓ : Type uℓ} [Field ℓ] [Algebra k ℓ]
    {a : k} {L : Type uL} [Field L] [Algebra (RatFunc k) L]
    (f : (RatFunc k)[X]) (hf : PolynomialRegularAt a f),
    f.Monic → (specialize a f hf).Separable →
    ∀ [Polynomial.IsSplittingField (RatFunc k) L f]
      [Polynomial.IsSplittingField k ℓ (specialize a f hf)]
      (i : PointEmbedding (ℓ := ℓ) a L),
    MatchesRoots i f hf →
    letI := residueAlgebra i
    ∃ e : residueField i.toRingHom ≃ₐ[k] ℓ, e.toRingHom = residueEmbedding i.toRingHom

/-- The decomposition group maps isomorphically onto the fibre Galois group by reduction. -/
abbrev DecompositionEquivalence : Prop :=
  ∀ {k : Type uk} [Field k] {ℓ : Type uℓ} [Field ℓ] [Algebra k ℓ]
    {a : k} {L : Type uL} [Field L] [Algebra (RatFunc k) L]
    (f : (RatFunc k)[X]) (hf : PolynomialRegularAt a f),
    f.Monic → (specialize a f hf).Separable →
    ∀ [Polynomial.IsSplittingField (RatFunc k) L f]
      [Polynomial.IsSplittingField k ℓ (specialize a f hf)]
      (i : PointEmbedding (ℓ := ℓ) a L),
    MatchesRoots i f hf →
    ∃ e : decompositionGroup i ≃* (ℓ ≃ₐ[k] ℓ),
      ∀ (σ : decompositionGroup i) (x : valuationRing i.toRingHom),
        e σ (reduction i.toRingHom x) = reduction i.toRingHom (onValuationRing i σ x)

end

end Specs.GaloisFormalization.IG.SpecializationDecomposition
