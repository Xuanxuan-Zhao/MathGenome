import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Arithmetic.ExceptionalLocalRootCoordinates
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Arithmetic.ExceptionalIwahoriCongruence

namespace LinearAlgebraicGroups.Specs.ExceptionalValuedScalarTransport

open AlgebraicGeometry CategoryTheory CategoryTheory.MonoidalCategory
open scoped CategoryTheory.MonObj
open Pinning (BasedRootDatum)
open AdjointRepresentation (GroupPoints)
open IntegralSemisimpleModel (IntegralPoints Model integerAlgebra)
open ExceptionalLocalRootCoordinates (LocalIwahori normalizedValuation)
open ExceptionalIwahoriImageComparison (integralUnitTorus)
open ExceptionalIwahoriCongruence (changeRingHom integralRing integralRingMap)
open SchemeDerivedGroup (FactorsThrough)

universe u

attribute [local instance] integerAlgebra

/-- Normalizing and factoring through the given closed torus can be
checked after an extension of the coefficient field, on the actual
point functor. This also applies to a coefficient automorphism. -/
def TorusConditions : Prop :=
  ∀ {F k k' : Type u} [Field F] [Field k] [Field k'] [Algebra F k] [Algebra F k']
    (G : GroupScheme F) (T : ClosedSubgroup G) (f : k →ₐ[F] k'),
    let s := (((groupPointsFunctor F).obj G).map (CommAlgCat.ofHom f)).hom
    ∀ x : GroupPoints G (CommAlgCat.of F k),
      (Normalizes T.inclusion (s x) ↔ Normalizes T.inclusion x) ∧
      (FactorsThrough T (s x) ↔ FactorsThrough T x)

/-- Valuation-preserving scalar maps pull back Borel reduction and unit
torus conditions and preserve the marked normalizer labels and integral
translation logs. Applies to both inclusion of splitting fields and
valuation-preserving coefficient automorphisms. -/
def ValuedTransport : Prop :=
  ∀ {L K : Type u} [Field L] [Field K]
    [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
    [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    {D : BasedRootDatum.{u}} {M : Model D}
    {G H : Type u} [Group G] [Group H] {W : Type u} [Group W]
    (j : G →* IntegralPoints M.group (integralRing L))
    (j' : H →* IntegralPoints M.group (integralRing K))
    (P : LocalIwahori j W) (P' : LocalIwahori j' W)
    (q : W →* D.datum.weylGroup), Function.Injective q →
    (∀ w, ∀ a ∈ P.normalizer.word w, a ∈ D.base.support) →
    (∀ w, ∀ a ∈ P'.normalizer.word w, a ∈ D.base.support) →
    (∀ w, ((P.normalizer.word w).map (RootPairing.weylGroup.ofIdx D.datum)).prod = q w) →
    (∀ w, ((P'.normalizer.word w).map (RootPairing.weylGroup.ofIdx D.datum)).prod = q w) →
    ∀ (f : L →+* K) (s : G →* H),
      (∀ z, normalizedValuation K (f z) = normalizedValuation L z) →
      (∀ g, j' (s g) = changeRingHom M.group (integralRingMap f) (j g)) →
      P'.normalizer.normalizer.comap s = P.normalizer.normalizer →
      P'.normalizer.torus.comap s = P.normalizer.torus →
      let N := P.normalizer
      let N' := P'.normalizer
      let U := (integralUnitTorus (K := L) M).comap j
      let U' := (integralUnitTorus (K := K) M).comap j'
      P'.iwahori.comap s = P.iwahori ∧ U'.comap s = U ∧
      ∀ (n : N.normalizer) (n' : N'.normalizer), (n' : H) = s n →
        N'.label n' = N.label n ∧
        (N'.translation (N'.torusPart n')).toAdd = (N.translation (N.torusPart n)).toAdd

end LinearAlgebraicGroups.Specs.ExceptionalValuedScalarTransport
