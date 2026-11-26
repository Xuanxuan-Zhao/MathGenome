import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Arithmetic.ExceptionalLocalRootCoordinates

namespace LinearAlgebraicGroups.Specs.ExceptionalPinnedCentralCover

open CategoryTheory CategoryTheory.MonoidalCategory
open scoped CategoryTheory.MonObj
open Pinning (BasedRootDatum)
open IntegralSemisimpleModel (Model IntegralPoints Integers integerAlgebra)
open AutomorphismSequence (AdjointQuotient SplitSequence)
open PinnedPairDescent (DescendedPair)
open AdjointRepresentation (GroupPoints)
open ExceptionalMarkedRootDescent (MarkedFibre SimpleRootOrbit TransportedOrbit coordinatePointEquiv
  pinnedDiagram pinnedMarkedPoint quadraticIntegralAlgebra transportedLabels)
open ExceptionalIwahoriImageComparison (MarkedCentralCover integralPointHom integralUnitTorus
  pinnedGroundPoint pointHom)
open ExceptionalValuedTorusNormalizer (fixedWeylGroup markedDiagramEquiv)
open ExceptionalLocalRootCoordinates (LocalIwahori)

universe u

attribute [local instance] integerAlgebra

section Comparisons

/-- The descended central map intertwines the original integral central
map on all actual test-algebra points, so its comparison persists at a
coefficient level by evaluation in the compositum. -/
def DescendedPointMap : Prop :=
  ∀ {k K : Type u} [Field k] [Field K] [Algebra k K] [FiniteDimensional k K] [IsGalois k K]
  {D E : BasedRootDatum.{u}} {M : Model D} {M' : Model E}
  (c : MarkedCentralCover M M') (C : MarkedFibre M k) (C' : MarkedFibre M' k)
  {l : Aut C.realization.attached.toBased ≃* Aut C.realization.pinned}
  {l' : Aut C'.realization.attached.toBased ≃* Aut C'.realization.pinned}
  {Q : AdjointQuotient C.realization.pinned.pair.G} {Q' : AdjointQuotient C'.realization.pinned.pair.G}
  {ω : Gal(K/k) →* Aut C.realization.attached.toBased}
  {ω' : Gal(K/k) →* Aut C'.realization.attached.toBased}
  (d : DescendedPair K (l := l) ω) (d' : DescendedPair K (l := l') ω') (σ : Gal(K/k)),
  E.datum.rootSpan ℤ = ⊤ →
  SplitSequence C.realization.pinned C.realization.attached l Q →
  SplitSequence C'.realization.pinned C'.realization.attached l' Q' →
  Module.finrank k K = 2 → σ ≠ 1 →
  let τ := (markedDiagramEquiv C.realization (d.data.outer σ)).asIso.hom
  let τ' := (markedDiagramEquiv C'.realization (d'.data.outer σ)).asIso.hom
  (∀ i, c.rootEquiv (τ.val.indexEquiv i) = τ'.val.indexEquiv (c.rootEquiv i)) →
  ∃ φ : d.group.val ⟶ d'.group.val,
    CentralIsogenies.IsCentralIsogeny φ ∧
      ∀ (R : TestAlgebra k) (g : GroupPoints d.group.val R),
        pinnedMarkedPoint C' d'.data R ((coordinatePointEquiv d'.group R).symm
          (pointHom φ ((testSpec k).obj (.op R)) g)) =
        integralPointHom c.map ((quadraticIntegralAlgebra k K).obj R)
          (pinnedMarkedPoint C d.data R ((coordinatePointEquiv d.group R).symm g))

/-- The induced map on a valued pair compares the actual rational
Iwahori and normalizer. The labels use the marked finite Weyl action
and the pushforward on integral cocharacters. -/
def LocalComparison : Prop :=
  ∀ {k K : Type u} [Field k] [Field K] [Algebra k K] [FiniteDimensional k K] [IsGalois k K]
  [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  {D E : BasedRootDatum.{u}} {M : Model D} {M' : Model E}
  (c : MarkedCentralCover M M') (C : MarkedFibre M k) (C' : MarkedFibre M' k)
  {l : Aut C.realization.attached.toBased ≃* Aut C.realization.pinned}
  {l' : Aut C'.realization.attached.toBased ≃* Aut C'.realization.pinned}
  {Q : AdjointQuotient C.realization.pinned.pair.G} {Q' : AdjointQuotient C'.realization.pinned.pair.G}
  {ω : Gal(K/k) →* Aut C.realization.attached.toBased}
  {ω' : Gal(K/k) →* Aut C'.realization.attached.toBased}
  (d : DescendedPair K (l := l) ω) (d' : DescendedPair K (l := l') ω') (σ : Gal(K/k)),
  E.datum.rootSpan ℤ = ⊤ →
  SplitSequence C.realization.pinned C.realization.attached l Q →
  SplitSequence C'.realization.pinned C'.realization.attached l' Q' →
  Module.finrank k K = 2 → σ ≠ 1 →
  (∀ a b, D.datum.pairing a b = D.datum.pairing b a) →
  (∀ a b, E.datum.pairing a b = E.datum.pairing b a) →
  let τ := (markedDiagramEquiv C.realization (d.data.outer σ)).asIso.hom
  let τ' := (markedDiagramEquiv C'.realization (d'.data.outer σ)).asIso.hom
  let W := fixedWeylGroup D τ
  let W' := fixedWeylGroup E τ'
  (∀ i, c.rootEquiv (τ.val.indexEquiv i) = τ'.val.indexEquiv (c.rootEquiv i)) →
  let R := CommAlgCat.of Integers.{u} K
  let G := (𝟙_ (SchemeOver k) ⟶ d.group.val.X)
  let H := (𝟙_ (SchemeOver k) ⟶ d'.group.val.X)
  ∀ (j : G →* IntegralPoints M.group R) (j' : H →* IntegralPoints M'.group R),
    Function.Injective j' →
    (∀ g, j g = pinnedGroundPoint C d.data g) →
    (∀ g, j' g = pinnedGroundPoint C' d'.data g) →
  ∀ (P : LocalIwahori j W) (P' : LocalIwahori j' W'),
    (∀ g : G, g ∈ P.normalizer.normalizer ↔ Normalizes d.torus.inclusion g) →
    (∀ g : H, g ∈ P'.normalizer.normalizer ↔ Normalizes d'.torus.inclusion g) →
    (∀ g : G, g ∈ P.normalizer.torus ↔ SchemeDerivedGroup.FactorsThrough d.torus g) →
    (∀ g : H, g ∈ P'.normalizer.torus ↔ SchemeDerivedGroup.FactorsThrough d'.torus g) →
    (∀ w, ∀ i ∈ P.normalizer.word w, i ∈ D.base.support) →
    (∀ w, ∀ i ∈ P'.normalizer.word w, i ∈ E.base.support) →
    (∀ w, ((P.normalizer.word w).map (RootPairing.weylGroup.ofIdx D.datum)).prod = w.val) →
    (∀ w, ((P'.normalizer.word w).map (RootPairing.weylGroup.ofIdx E.datum)).prod = w.val) →
  ∀ (φ : G →* H), (∀ g, j' (φ g) = integralPointHom c.map R (j g)) →
    let N := P.normalizer
    let N' := P'.normalizer
    let U := (integralUnitTorus (K := K) M).comap j
    let U' := (integralUnitTorus (K := K) M').comap j'
    P'.iwahori.comap φ = P.iwahori ∧
    (∀ h, h ∈ P'.iwahori ↔ ∃ (g : P.iwahori) (t : U'), h = φ g * t) ∧
    N'.normalizer.comap φ = N.normalizer ∧ N'.torus.comap φ = N.torus ∧
    U'.comap φ = U ∧ φ.range.Normal ∧
    ∃ e : D.datum.weylGroup ≃* E.datum.weylGroup,
      (∀ i, e (RootPairing.weylGroup.ofIdx D.datum i) =
        RootPairing.weylGroup.ofIdx E.datum (c.rootEquiv i)) ∧
      (∀ (n : N.normalizer) (n' : N'.normalizer), (n' : H) = φ n →
        (N'.label n').val = e (N.label n).val ∧
        (N'.translation (N'.torusPart n')).toAdd =
          c.pushCocharacter (N.translation (N.torusPart n)).toAdd)

end Comparisons
end LinearAlgebraicGroups.Specs.ExceptionalPinnedCentralCover
