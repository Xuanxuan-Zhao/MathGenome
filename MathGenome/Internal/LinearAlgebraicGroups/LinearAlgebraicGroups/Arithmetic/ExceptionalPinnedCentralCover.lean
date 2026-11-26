import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Arithmetic.ExceptionalPinnedCentralCover
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.ExceptionalIwahoriImageComparison
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.ExceptionalLocalRootCoordinates
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.ExceptionalValuedTorusNormalizer
import Batteries.Tactic.OpenPrivate

namespace LinearAlgebraicGroups.Arithmetic.ExceptionalPinnedCentralCover

open AlgebraicGeometry CategoryTheory CategoryTheory.MonoidalCategory WithConv ValuativeRel
open CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj TensorProduct
open _root_.LinearAlgebraicGroups.Specs
open Specs.ExceptionalPinnedCentralCover
open Specs.IntegralSemisimpleModel
open Specs.AdjointCocharacters (coordinateHopfMap)
open Specs.ExceptionalMarkedRootDescent
open Specs.ExceptionalIwahoriImageComparison
open Arithmetic.ExceptionalIwahoriImageComparison
open private coordinatePointEquiv_comp restrictExtended_comp
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.ExceptionalMarkedRootDescent
open private markedFibrePoint_natural centralCover_diagramEquivariant
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.ExceptionalIwahoriImageComparison

universe u

noncomputable section

attribute [local instance] integerAlgebra

set_option backward.isDefEq.respectTransparency false in
/-- Evaluate the descended Hopf square after scalar extension of any test algebra. -/
theorem descendedCentralMap : DescendedPointMap.{u} := by
  intro k K _ _ _ _ _ D E M M' c C C' l l' Q Q' ω ω' d d' σ hE hQ hQ' hd hσ τ τ' hdiag
  obtain ⟨p, _, _, hp, _, _, _, _, _, _, h, _⟩ :=
    pinnedCentralCoverComparison c hE C C' hQ hQ' d d' hd σ hσ hdiag
  refine ⟨p, hp, ?_⟩
  intro R g
  let U := (extendedTestAlgebra k K).obj R
  let f := C.groupIso.inv ≫ (fibre k).map c.map ≫ C'.groupIso.hom
  let π := coordinateHopfMap (G := d.group) (H := d'.group) p
  let ψ := coordinateHopfMap (G := C.realization.pinned.pair.G) (H := C'.realization.pinned.pair.G) f
  let a := (coordinatePointEquiv d.group R).symm g
  have ha : (coordinatePointEquiv d'.group R).symm (pointHom p ((testSpec k).obj (.op R)) g) =
      toConv (a.ofConv.comp π.hom.toAlgHom) := by
    apply (coordinatePointEquiv d'.group R).injective
    rw [MulEquiv.apply_symm_apply, coordinatePointEquiv_comp (G := d.group) (H := d'.group) p R a]
    exact congrArg (· ≫ p.hom.hom) ((coordinatePointEquiv d.group R).apply_symm_apply g).symm
  have he : extendAlgebraPoint (K := K) (a.ofConv.comp π.hom.toAlgHom) =
      (extendAlgebraPoint a.ofConv).comp (extendedHopfMap K π).hom.toAlgHom := by
    apply Algebra.TensorProduct.ext_ring
    apply AlgHom.ext
    intro x
    change extendAlgebraPoint (K := K) (a.ofConv.comp π.hom.toAlgHom) (1 ⊗ₜ[k] x) =
      extendAlgebraPoint (K := K) a.ofConv (1 ⊗ₜ[k] π.hom x)
    simp only [extendAlgebraPoint, AlgHom.liftEquiv_tmul, AlgHom.comp_apply]
    rfl
  have hs : pinnedAlgebraPointMap d'.data (a.ofConv.comp π.hom.toAlgHom) =
      (pinnedAlgebraPointMap d.data a.ofConv).comp (extendedHopfMap K ψ).hom.toAlgHom := by
    unfold pinnedAlgebraPointMap
    rw [he]
    apply AlgHom.ext
    intro x
    exact congrArg (extendAlgebraPoint (K := K) a.ofConv) (ConcreteCategory.congr_hom h x)
  rw [ha]
  have hscheme : pinnedSchemePoint d'.data R (toConv (a.ofConv.comp π.hom.toAlgHom)) =
      pinnedSchemePoint d.data R a ≫ f.hom.hom := by
    unfold pinnedSchemePoint
    rw [ofConv_toConv, hs, restrictExtended_comp (K := K) R ψ]
    exact coordinatePointEquiv_comp (G := C.realization.pinned.pair.G)
      (H := C'.realization.pinned.pair.G) f U _
  unfold pinnedMarkedPoint
  rw [hscheme]
  exact markedFibrePoint_natural c C C' U _

section LocalNormalizer

open AlgebraicGeometry
open Specs.Pinning (BasedRootDatum)
open Specs.ExceptionalValuedTorusNormalizer (FibreNormalizer valuationRingInclusion)
open Arithmetic.ExceptionalValuedTorusNormalizer (fibreNormalizerTorusAction integralTorusCoordinates)
open private cover_simple splitMarkedNormalizerWord localNormalizer_unitKernel
  valuationRingTorusPoint unit_character_of_finite_index
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.ExceptionalIwahoriImageComparison
open private markedWeylWord_map markedTorusPoint_map
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.ExceptionalMarkedRootDescent
open private liftIntegralClosedPoint
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.ExceptionalLocalRootCoordinates
open private affineTorusPointEquiv
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Classification.IntegralSemisimpleModel

variable {K : Type u} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]
  {D E : BasedRootDatum.{u}} {M : Model D} {M' : Model E}
  (c : MarkedCentralCover M M')
  {G H W W' : Type u} [Group G] [Group H] [Group W] [Group W']
  {j : G →* IntegralPoints M.group (CommAlgCat.of Integers.{u} K)}
  {j' : H →* IntegralPoints M'.group (CommAlgCat.of Integers.{u} K)}
  (N : MarkedLocalNormalizer K j W) (N' : MarkedLocalNormalizer K j' W')
  (p : G →* H)
  (hcomm : ∀ g, j' (p g) = integralPointHom c.map _ (j g))

include hcomm

set_option backward.isDefEq.respectTransparency false in
private theorem integralUnit_preimage
    (hT : N'.torus.comap p = N.torus) :
    ((integralUnitTorus (K := K) M').comap j').comap p =
      (integralUnitTorus (K := K) M).comap j := by
  let R := CommAlgCat.of Integers.{u} K
  let S := CommAlgCat.of Integers.{u} (valuation K).valuationSubring
  let i := valuationRingInclusion K
  let χ := c.pullCharacter.toAddMonoidHom.toMultiplicative
  have := c.characterIndex
  have := D.freeY
  have := D.finiteY
  let b := Module.Free.chooseBasis ℤ D.Y
  ext g
  change j' (p g) ∈ integralUnitTorus (K := K) M' ↔
    j g ∈ integralUnitTorus (K := K) M
  constructor
  · intro hg
    have ht' : p g ∈ N'.torus := by
      have hu : p g ∈ (integralUnitTorus (K := K) M').comap j' := hg
      rw [← localNormalizer_unitKernel N'] at hu
      obtain ⟨t, _, ht⟩ := hu
      exact ht ▸ t.property
    have ht : g ∈ N.torus := hT ▸ (show g ∈ N'.torus.comap p from ht')
    obtain ⟨v, hv⟩ := (N.torusPoints g).mp ht
    obtain ⟨s, hs⟩ := hg
    obtain ⟨z, rfl⟩ :=
      (affineTorusPointEquiv (k := Integers.{u}) (M := Multiplicative E.X) S).surjective s
    have hval : v.comp χ = (Units.map i.hom.toMonoidHom).comp z := by
      have h := (hcomm g).trans ((congrArg (integralPointHom c.map R) hv).trans (c.marking.2.2 R v))
      have hh := (valuationRingTorusPoint M' z).symm.trans (hs.trans h)
      let _ := M'.torusClosed
      have : Mono M'.torus.hom.hom := Over.mono_of_mono_left _
      exact (affineTorusPointEquiv (k := Integers.{u}) R).injective
        ((cancel_mono M'.torus.hom.hom).mp hh.symm)
    have hv' (x : Multiplicative E.X) :
        normalizedValuation K (v (χ x) : K) = 1 := by
      change normalizedValuation K ((v.comp χ) x : K) = 1
      rw [hval]
      let y := ((Units.map i.hom.toMonoidHom).comp z) x
      have hy : valuation K (y : K) ≤ 1 := (↑(z x) : (valuation K).valuationSubring).property
      have hy' : valuation K (↑(y⁻¹) : K) ≤ 1 := by
        change valuation K (↑((Units.map i.hom.toMonoidHom (z x))⁻¹) : K) ≤ 1
        rw [← map_inv]
        exact (↑((z x)⁻¹) : (valuation K).valuationSubring).property
      have he : valuation K (y : K) = 1 := by
        have hy₀ : 0 < valuation K (y : K) :=
          pos_iff_ne_zero.mpr ((map_ne_zero _).mpr y.ne_zero)
        rw [Units.val_inv_eq_inv_val, map_inv₀, inv_le_one₀ hy₀] at hy'
        exact le_antisymm hy hy'
      change IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt K (valuation K (y : K)) = 1
      rw [he, map_one]
    obtain ⟨t, ht⟩ := (integralTorusCoordinates D b v).mp (fun x =>
      unit_character_of_finite_index χ v hv' _)
    exact ⟨torusPoint D S t, (valuationRingTorusPoint M t).trans
      ((congrArg (fun z => torusPoint D R z ≫ M.torus.hom.hom) ht).trans hv.symm)⟩
  · rintro ⟨s, hs⟩
    obtain ⟨z, rfl⟩ :=
      (affineTorusPointEquiv (k := Integers.{u}) (M := Multiplicative D.X) S).surjective s
    refine ⟨torusPoint E S (z.comp χ), ?_⟩
    calc
      _ = torusPoint E R (((Units.map i.hom.toMonoidHom).comp z).comp χ) ≫ M'.torus.hom.hom :=
        valuationRingTorusPoint M' (z.comp χ)
      _ = integralPointHom c.map R (j g) := (c.marking.2.2 R _).symm.trans
        (congrArg (integralPointHom c.map R) ((valuationRingTorusPoint M z).symm.trans hs))
      _ = _ := (hcomm g).symm

set_option backward.isDefEq.respectTransparency false in
private theorem normalizerLabels (F : FibreNormalizer M' K)
    (e : D.datum.weylGroup ≃* E.datum.weylGroup)
    (he : ∀ a, e (RootPairing.weylGroup.ofIdx D.datum a) =
      RootPairing.weylGroup.ofIdx E.datum (c.rootEquiv a))
    (q : W →* D.datum.weylGroup) (q' : W' →* E.datum.weylGroup)
    (eqFixed : W ≃* W') (hFixed : ∀ w, q' (eqFixed w) = e (q w))
    (hw : ∀ w, ∀ a ∈ N.word w, a ∈ D.base.support)
    (hw' : ∀ w, ∀ a ∈ N'.word w, a ∈ E.base.support)
    (hprod : ∀ w, ((N.word w).map (RootPairing.weylGroup.ofIdx D.datum)).prod = q w)
    (hprod' : ∀ w, ((N'.word w).map (RootPairing.weylGroup.ofIdx E.datum)).prod = q' w)
    (hT : N'.torus.comap p = N.torus) :
    ∀ (n : N.normalizer) (n' : N'.normalizer), (n' : H) = p n →
      q' (N'.label n') = e (q (N.label n)) ∧
      (N'.translation (N'.torusPart n')).toAdd =
        c.pushCocharacter (N.translation (N.torusPart n)).toAdd := by
  intro n n' hn
  let R := CommAlgCat.of Integers.{u} K
  let S := CommAlgCat.of Integers.{u} (valuation K).valuationSubring
  let i := valuationRingInclusion K
  let w := N.label n
  let w' := eqFixed w
  let a := (N.word w).map c.rootEquiv
  let b := N'.word w'
  have ha : ∀ x ∈ a, x ∈ E.base.support := by
    intro x hx
    obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hx
    exact (cover_simple c y).mp (hw w y hy)
  obtain ⟨m₁, hm₁, hq₁⟩ := splitMarkedNormalizerWord F a ha
  obtain ⟨m₂, hm₂, hq₂⟩ := splitMarkedNormalizerWord F b (hw' w')
  have hq : F.label m₁ = F.label m₂ := by
    rw [hq₁, hq₂, hprod', hFixed, ← hprod w]
    simp only [a, List.map_map, Function.comp_def, map_list_prod, he]
  let m : F.label.ker := ⟨m₁ * m₂⁻¹, by simp [hq]⟩
  obtain ⟨φ, hφ, _⟩ := fibreNormalizerTorusAction F
  obtain ⟨s, hs⟩ := φ.surjective m
  let r := p (N.lift w) * (N'.lift w' : H)⁻¹
  have hr : j' r = F.point m.val := by
    change j' (p (N.lift w) * (N'.lift w' : H)⁻¹) = F.point (m₁ * m₂⁻¹)
    rw [map_mul, map_inv, map_mul, map_inv, hcomm, N.lift_point, N'.lift_point, hm₁, hm₂]
    rw [(markedRankOneMapCompatibility c.map c.rootEquiv _ c.marking (fun x => c.reflections x x)).2]
  have hrs : j' r = torusPoint E R s ≫ M'.torus.hom.hom :=
    hr.trans ((congrArg (fun x : F.label.ker => F.point x.val) hs).symm.trans (hφ s))
  let ρ : N'.torus := ⟨r, (N'.torusPoints r).mpr ⟨s, hrs⟩⟩
  have hρ : N'.translation ρ = 1 := by
    let z := markedWeylWord M'.toIntegralMarking S a *
      (markedWeylWord M'.toIntegralMarking S b)⁻¹
    have hz : (integralPointFunctor M'.group).map i z = j' r := by
      change (((integralPointFunctor M'.group).map i).hom) z = _
      rw [hr]
      change _ = F.point (m₁ * m₂⁻¹)
      calc
        _ = markedWeylWord M'.toIntegralMarking R a *
              (markedWeylWord M'.toIntegralMarking R b)⁻¹ := by
          change ((integralPointFunctor M'.group).map i).hom
            (markedWeylWord M'.toIntegralMarking S a * (markedWeylWord M'.toIntegralMarking S b)⁻¹) = _
          rw [map_mul, map_inv]
          exact congrArg₂ (fun x y : IntegralPoints M'.group R => x * y⁻¹)
            (markedWeylWord_map _ i a) (markedWeylWord_map _ i b)
        _ = F.point (m₁ * m₂⁻¹) := by rw [F.point.map_mul, F.point.map_inv, hm₁, hm₂]
    let _ := M'.torusClosed
    obtain ⟨z₀, hz₀⟩ := liftIntegralClosedPoint M'.torus.hom.hom i
      (show Function.Injective i.hom from Subtype.val_injective) z (torusPoint E R s) (hz.trans hrs)
    have hU : r ∈ (integralUnitTorus (K := K) M').comap j' := by
      refine ⟨z₀, ?_⟩
      change (integralPointFunctor (splitTorus E)).map i z₀ ≫ M'.torus.hom.hom = _
      exact (markedTorusPoint_map M'.toIntegralMarking i z₀).symm.trans
        ((congrArg (fun x : IntegralPoints M'.group S => (integralPointFunctor M'.group).map i x) hz₀).trans hz)
    rw [← localNormalizer_unitKernel N'] at hU
    obtain ⟨y, hy, hye⟩ := hU
    have h : y = ρ := Subtype.ext hye
    exact h ▸ hy
  let pt : N'.torus :=
    ⟨p (N.torusPart n), show (N.torusPart n : G) ∈ N'.torus.comap p by
      rw [hT]
      exact (N.torusPart n).property⟩
  have hpt : (N'.translation pt).toAdd = c.pushCocharacter (N.translation (N.torusPart n)).toAdd := by
    obtain ⟨v, hv⟩ := (N.torusPoints (N.torusPart n)).mp (N.torusPart n).property
    have hv' : j' pt = torusPoint E R (v.comp c.pullCharacter.toAddMonoidHom.toMultiplicative) ≫
        M'.torus.hom.hom :=
      (hcomm _).trans ((congrArg (integralPointHom c.map R) hv).trans (c.marking.2.2 R v))
    exact (markedTranslationCompatibility D E c.pullCharacter c.pushCocharacter c.pairing v
      _ _ (N.characterLog _ v hv) (N'.characterLog pt _ hv')).1.symm
  let t := pt * ρ
  let tN : N'.normalizer := ⟨t, N'.torus_le t.property⟩
  have hsplit : n' = tN * N'.lift w' := by
    apply Subtype.ext
    change (n' : H) = (p (N.torusPart n) * r) * N'.lift w'
    rw [hn]
    change p n = (p ((n : G) * (N.lift w : G)⁻¹) *
      (p (N.lift w) * (N'.lift w' : H)⁻¹)) * N'.lift w'
    simp only [map_mul, map_inv]
    group
  have hlabel : N'.label n' = w' := by
    have ht : N'.label tN = 1 := (N'.labelKernel tN).mpr t.property
    rw [hsplit, map_mul, ht, one_mul, N'.lift_label]
  have htorus : N'.torusPart n' = t := by
    apply Subtype.ext
    change (n' : H) * (N'.lift (N'.label n') : H)⁻¹ = (t : H)
    rw [hlabel, hsplit]
    exact mul_inv_cancel_right _ _
  refine ⟨(congrArg q' hlabel).trans (hFixed w), ?_⟩
  rw [htorus, show t = pt * ρ from rfl, map_mul, hρ, mul_one]
  exact hpt

end LocalNormalizer

section SplitFactors

open Opposite
open Specs.Pinning (BasedRootDatum PinnedIso)
open Specs.AdjointRepresentation (GroupPoints)
open Specs.AdjointBorelCohomology (PinnedTwist)
open Specs.AbstractPairing (Root)
open Specs.BorelsAndChambers (subgroupRoots IsPositiveSystem)
open Specs.OrderedRootProducts (Enumerates)
open Specs.RankOneFlag (SameSubgroup)
open Specs.Unipotent (closedSubgroupAlgebraicGroup)
open Specs.GeometricBorelConjugacy (IsKBorel)
open Specs.SchemeDerivedGroup (IsSubgroupOf)
open private fibrePointEquiv fibrePointEquiv_apply markedTorusEquiv markedTorusIncl
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.ExceptionalMarkedRootDescent
open private markedProduct_range pinnedGroundPoint_range
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.ExceptionalIwahoriImageComparison
open private basedIso_pos_iff base_isPos_iff_subgroupRoots pushKBorel
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Classification.PinnedEquivalence
open private weightSpace_le_lieImage_iff rootsOfIso
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.RootData.BorelsAndChambers
open private subgroupIso from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.RootData.OrderedRootProducts
open private transportSubgroup radical_transport unipotent_of_iso
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Reductive.RadicalBaseChange

variable {k K : Type u} [Field k] [Field K] [Algebra k K]
  {D : BasedRootDatum.{u}} {M : Model D} (C : MarkedFibre M k)

set_option backward.isDefEq.respectTransparency false in
private def splitPointAction (s : PinnedIso C.realization.pinned C.realization.pinned)
    (σ : Gal(K/k)) : IntegralPoints M.group (CommAlgCat.of Integers.{u} K) →*
      IntegralPoints M.group (CommAlgCat.of Integers.{u} K) :=
  let R := CommAlgCat.of k K
  let e := fibrePointEquiv C R
  e.toMonoidHom.comp
    ((MonoidHom.mk' (fun g : GroupPoints C.realization.pinned.pair.G.val R =>
      (testSpec k).map (CommAlgCat.ofHom σ.toAlgHom).op ≫ g ≫ s.group.hom.hom.hom)
        (fun a b => by
          let f := (testSpec k).map (CommAlgCat.ofHom σ.toAlgHom).op
          let h := s.group.hom.hom.hom
          change f ≫ (a * b) ≫ h = (f ≫ a ≫ h) * (f ≫ b ≫ h)
          rw [← Category.assoc f, MonObj.comp_mul, MonObj.mul_comp]
          simp only [Category.assoc])).comp e.symm.toMonoidHom)

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 800000 in
private theorem splitPointAction_apply
    (s : PinnedIso C.realization.pinned C.realization.pinned) (σ : Gal(K/k))
    (x : GroupPoints C.realization.pinned.pair.G.val (CommAlgCat.of k K)) :
    splitPointAction C s σ (markedFibrePoint C (CommAlgCat.of k K) x) =
      markedFibrePoint C (CommAlgCat.of k K) ((testSpec k).map (CommAlgCat.ofHom σ.toAlgHom).op ≫ x ≫
        s.group.hom.hom.hom) := by
  let R := CommAlgCat.of k K
  let e := fibrePointEquiv C R
  let a := (testSpec k).map (CommAlgCat.ofHom σ.toAlgHom).op
  change e (a ≫ e.symm (e x) ≫ s.group.hom.hom.hom) = e (a ≫ x ≫ s.group.hom.hom.hom)
  rw [MulEquiv.symm_apply_apply]

set_option backward.isDefEq.respectTransparency false in
private theorem stableSplitTorus
    (s : PinnedIso C.realization.pinned C.realization.pinned) (σ : Gal(K/k))
    (t : IntegralPoints (splitTorus D) (CommAlgCat.of Integers.{u} K)) :
    ∃ t', splitPointAction C s σ (t ≫ M.torus.hom.hom) = t' ≫ M.torus.hom.hom := by
  let R := CommAlgCat.of k K
  let T := C.realization.pinned.pair.T
  let z := (markedTorusEquiv C R).symm t
  let a := (testSpec k).map (CommAlgCat.ofHom σ.toAlgHom).op
  have ht : markedFibrePoint C R (z ≫ T.inclusion.hom.hom) = t ≫ M.torus.hom.hom := by
    exact (markedTorusIncl C R z).trans
      (congrArg (fun w : IntegralPoints (splitTorus D) (CommAlgCat.of Integers.{u} K) =>
        w ≫ M.torus.hom.hom) ((markedTorusEquiv C R).apply_symm_apply t))
  have hs := congrArg (fun f : T.group ⟶ C.realization.pinned.pair.G.val => f.hom.hom) s.torus_comm
  refine ⟨markedTorusEquiv C R (a ≫ z ≫ s.torus.hom.hom.hom), ?_⟩
  rw [← ht, splitPointAction_apply]
  have hz := markedTorusIncl C R (a ≫ z ≫ s.torus.hom.hom.hom)
  refine (congrArg (markedFibrePoint C R) ?_).trans hz
  change a ≫ (z ≫ T.inclusion.hom.hom) ≫ s.group.hom.hom.hom =
    (a ≫ z ≫ s.torus.hom.hom.hom) ≫ T.inclusion.hom.hom
  change T.inclusion.hom.hom ≫ s.group.hom.hom.hom =
    s.torus.hom.hom.hom ≫ T.inclusion.hom.hom at hs
  simp only [Category.assoc, hs]


set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 1300000 in
private theorem stableSplitRoots
    (s : PinnedIso C.realization.pinned C.realization.pinned) (σ : Gal(K/k))
    (L : List D.I) (positive : Bool)
    (hL : Enumerates L {a | if positive then D.base.IsPos a else ¬ D.base.IsPos a})
    {g : IntegralPoints M.group (CommAlgCat.of Integers.{u} K)}
    (hg : g ∈ Set.range (orderedRootPoint M.toIntegralMarking _ L)) :
    splitPointAction C s σ g ∈ Set.range (orderedRootPoint M.toIntegralMarking _ L) := by
  let P := C.realization.pinned
  let T := P.pair.T
  let B := P.pair.B
  let F := s.group
  let t := s.torus
  let R := CommAlgCat.of k K
  let A := (testSpec k).map (CommAlgCat.ofHom σ.toAlgHom).op
  have ht : T.inclusion ≫ F.hom = t.hom ≫ T.inclusion := s.torus_comm
  obtain ⟨_, _, _, hc, _, _, hdec⟩ :=
    RootData.BorelPositivity.borelPositivity P.pair.G P.pair.reductive T P.pair.split P.pair.maximal
  have hb := hc.1 B P.pair.borel P.pair.containsTorus
  let S : Set (Root T) := if positive then subgroupRoots T B else (subgroupRoots T B)ᶜ
  have hS : IsPositiveSystem T S := by
    cases positive
    · obtain ⟨f, hn, hf⟩ := hb
      refine ⟨-f, fun i => neg_ne_zero.mpr (hn i), ?_⟩
      change (subgroupRoots T B)ᶜ = _
      rw [hf]
      ext i
      change (¬ 0 < f (Additive.ofMul i.val)) ↔ 0 < -f (Additive.ofMul i.val)
      rw [neg_pos, not_lt]
      exact le_iff_lt_or_eq.trans (or_iff_left (hn i))
    · exact hb
  obtain ⟨B₁, hB₁, ht₁, hroots⟩ := hc.2.1 S hS
  let B₂ := transportSubgroup F B₁
  have ht₂ : IsSubgroupOf T B₂ := by
    obtain ⟨v, hv⟩ := ht₁
    refine ⟨t.inv ≫ v, ?_⟩
    change (t.inv ≫ v) ≫ B₁.inclusion ≫ F.hom = T.inclusion
    simp only [Category.assoc, reassoc_of% hv, ht, Iso.inv_hom_id_assoc]
  have hsame : subgroupRoots T B₂ = subgroupRoots T B₁ := by
    ext α
    have hr := weightSpace_le_lieImage_iff F t ht (B := B₁) (C := B₂) (Iso.refl _)
      (by change _ = 𝟙 _ ≫ _; rw [Category.id_comp]; rfl) α.val
    have hb' := weightSpace_le_lieImage_iff F t ht s.borel s.borel_comm α.val
    have hα : t.hom ≫ α.val ∈ Specs.CharacterPairing.absoluteRoots T :=
      (rootsOfIso F t ht α.val).mpr α.property
    let β : Root T := ⟨t.hom ≫ α.val, hα⟩
    change β ∈ subgroupRoots T B₁ ↔ α ∈ subgroupRoots T B₂ at hr
    change β ∈ subgroupRoots T B ↔ α ∈ subgroupRoots T B at hb'
    rw [← hr, hroots]
    cases positive
    · exact not_congr hb'
    · exact hb'
  let b := subgroupIso ((hc.2.2 B₂ B₁ (pushKBorel F hB₁) hB₁ ht₂ ht₁).mp hsame)
  have hb₁ : B₁.inclusion ≫ F.hom = b.val.hom ≫ B₁.inclusion := b.property.symm
  obtain ⟨U, _, _, hU, _, _, _, _, _, hparam⟩ := hdec B₁ hB₁ ht₁
  let U' := transportSubgroup b.val U
  have hU' := radical_transport (G := closedSubgroupAlgebraicGroup B₁)
    (G' := closedSubgroupAlgebraicGroup B₁) b.val Specs.Unipotent.IsUnipotent
    (fun e _ _ => unipotent_of_iso e) U hU
  obtain ⟨u, hu⟩ := hU.2.2 U' hU'.1 hU'.2.1
  let e := C.realization.datumIso.val.indexEquiv
  have hpos (a : D.I) : D.base.IsPos a ↔ e a ∈ subgroupRoots T B :=
    (basedIso_pos_iff C.realization.datumIso a).trans
      (base_isPos_iff_subgroupRoots C.realization.attached hb (e a))
  have he : Enumerates (L.map e) (subgroupRoots T B₁) := by
    refine ⟨hL.1.map e.injective, ?_⟩
    intro α
    obtain ⟨a, rfl⟩ := e.surjective α
    rw [List.mem_map_of_injective e.injective, hL.2 a, hroots]
    cases positive
    · exact not_congr (hpos a)
    · exact hpos a
  obtain ⟨v, hv⟩ := hparam P.roots (L.map e) he
  let inclusion := U.inclusion ≫ B₁.inclusion
  have hi : inclusion ≫ F.hom = u ≫ inclusion := by
    change (U.inclusion ≫ B₁.inclusion) ≫ F.hom = u ≫ (U.inclusion ≫ B₁.inclusion)
    change u ≫ U.inclusion = U.inclusion ≫ b.val.hom at hu
    rw [Category.assoc, hb₁, ← Category.assoc U.inclusion, ← hu, Category.assoc]
  rw [← markedProduct_range C R L hL.1] at hg ⊢
  obtain ⟨x, rfl⟩ := hg
  let y := A ≫ x ≫ v.hom ≫ u.hom.hom ≫ v.inv
  refine ⟨y, ?_⟩
  change markedFibrePoint C R _ = splitPointAction C s σ (markedFibrePoint C R _)
  rw [splitPointAction_apply]
  apply congrArg (markedFibrePoint C R)
  have hi₀ := congrArg (fun f : U.group ⟶ P.pair.G.val => f.hom.hom) hi
  simp only [Grp.comp_hom_hom, inclusion, Category.assoc] at hi₀
  change (A ≫ x ≫ v.hom ≫ u.hom.hom ≫ v.inv) ≫
      OrderedRootProducts.rootProduct P.roots (L.map e) =
    A ≫ (x ≫ OrderedRootProducts.rootProduct P.roots (L.map e)) ≫ F.hom.hom.hom
  rw [← hv]
  simp only [Category.assoc, Iso.inv_hom_id_assoc, hi₀]

open private positiveAndNegativeEnumerations
  enumerates_map orderedRootPoint_image orderedRootPoint_congr markedCellPoint_map
  iwahori_chart_factors reduction_contains_unitTorus
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.ExceptionalIwahoriImageComparison
open Arithmetic.ExceptionalMarkedRootDescent (markedCellCoordinates)
open Specs.ExceptionalValuedTorusNormalizer (valuationRingInclusion)
open Specs.AutomorphismSequence (AdjointQuotient SplitSequence)
open Specs.PinnedPairDescent (DescendedPair)

set_option backward.isDefEq.respectTransparency false in
private theorem splitAction_natural
    {E : BasedRootDatum.{u}} {M' : Model E} (C' : MarkedFibre M' k)
    (c : MarkedCentralCover M M') (σ : Gal(K/k))
    (s : PinnedIso C.realization.pinned C.realization.pinned)
    (s' : PinnedIso C'.realization.pinned C'.realization.pinned)
    (hf : let f := C.groupIso.inv ≫ (fibre k).map c.map ≫ C'.groupIso.hom
          f ≫ s'.group.hom = s.group.hom ≫ f) (x : IntegralPoints M.group (CommAlgCat.of Integers.{u} K)) :
    splitPointAction C' s' σ (integralPointHom c.map _ x) =
      integralPointHom c.map _ (splitPointAction C s σ x) := by
  let R := CommAlgCat.of k K
  let f := C.groupIso.inv ≫ (fibre k).map c.map ≫ C'.groupIso.hom
  let a := (testSpec k).map (CommAlgCat.ofHom σ.toAlgHom).op
  obtain ⟨g, hg⟩ := (fibrePointEquiv C R).surjective x
  change markedFibrePoint C R g = x at hg
  rw [← hg, ← markedFibrePoint_natural c C C' R, splitPointAction_apply,
    splitPointAction_apply, ← markedFibrePoint_natural c C C' R]
  apply congrArg (markedFibrePoint C' R)
  have he := congrArg (fun m : C.realization.pinned.pair.G.val ⟶ C'.realization.pinned.pair.G.val =>
    m.hom.hom) hf
  change f.hom.hom ≫ s'.group.hom.hom.hom = s.group.hom.hom.hom ≫ f.hom.hom at he
  change a ≫ (g ≫ f.hom.hom) ≫ s'.group.hom.hom.hom =
    (a ≫ g ≫ s.group.hom.hom.hom) ≫ f.hom.hom
  simp only [Category.assoc, he]

set_option backward.isDefEq.respectTransparency false in
private theorem splitPoint_fixed_iff [FiniteDimensional k K] [IsGalois k K]
    {l : Aut C.realization.attached.toBased ≃* Aut C.realization.pinned}
    {G : AffineAlgebraicGroup k} {B T : ClosedSubgroup G.val}
    (d : PinnedTwist K C.realization.attached l B T)
    (σ : Gal(K/k)) (hd : Module.finrank k K = 2) (hσ : σ ≠ 1)
    (x : IntegralPoints M.group (CommAlgCat.of Integers.{u} K)) :
    x ∈ Set.range (pinnedGroundPoint C d) ↔
      splitPointAction C (pinnedDiagram d σ).asIso.hom σ x = x := by
  let R := CommAlgCat.of k K
  let e := fibrePointEquiv C R
  obtain ⟨g, rfl⟩ := e.surjective x
  change markedFibrePoint C R g ∈ _ ↔
    splitPointAction C (pinnedDiagram d σ).asIso.hom σ (markedFibrePoint C R g) = _
  rw [pinnedGroundPoint_range C d σ hd hσ, splitPointAction_apply]
  refine ⟨congrArg (markedFibrePoint C R), fun h => ?_⟩
  apply e.injective
  exact h

set_option backward.isDefEq.respectTransparency false in
private theorem centralCell_unique
    {E : BasedRootDatum.{u}} {M' : Model E} (c : MarkedCentralCover M M')
    (R : IntegralAlgebra.{u}) (ns ps : List D.I)
    (hn : Enumerates ns {a | ¬ D.base.IsPos a}) (hp : Enumerates ps {a | D.base.IsPos a})
    (x y : D.I → R) (t t' : IntegralPoints (splitTorus E) R) :
    let f := integralPointHom c.map R
    let n := orderedRootPoint M.toIntegralMarking R ns
    let p := orderedRootPoint M.toIntegralMarking R ps
    f (n x) * ((t ≫ M'.torus.hom.hom) * f (p x)) =
      f (n y) * ((t' ≫ M'.torus.hom.hom) * f (p y)) →
    x = y ∧ t = t' := by
  intro f n p h
  obtain ⟨hn', hp'⟩ := enumerates_map c.rootEquiv c.marking.1 ns ps hn hp
  let a := x ∘ c.rootEquiv.symm
  let b := y ∘ c.rootEquiv.symm
  have ha : a ∘ c.rootEquiv = x := funext (fun i => congrArg x (c.rootEquiv.symm_apply_apply i))
  have hb : b ∘ c.rootEquiv = y := funext (fun i => congrArg y (c.rootEquiv.symm_apply_apply i))
  have hx (L : List D.I) := orderedRootPoint_image c.map c.rootEquiv R (c.marking.2.1 R) L a
  have hy (L : List D.I) := orderedRootPoint_image c.map c.rootEquiv R (c.marking.2.1 R) L b
  change f (orderedRootPoint M.toIntegralMarking R ns x) *
    ((t ≫ M'.torus.hom.hom) * f (orderedRootPoint M.toIntegralMarking R ps x)) =
    f (orderedRootPoint M.toIntegralMarking R ns y) *
    ((t' ≫ M'.torus.hom.hom) * f (orderedRootPoint M.toIntegralMarking R ps y)) at h
  simp only [ha] at hx
  simp only [hb] at hy
  rw [hx ns, hx ps, hy ns, hy ps] at h
  have he : (a, t) = (b, t') :=
    (markedCellCoordinates M'.toIntegralMarking R _ _ hn' hp').1 h
  refine ⟨ha.symm.trans ((congrArg (fun z => z.1 ∘ c.rootEquiv) he).trans hb), congrArg Prod.snd he⟩

open Specs.ExceptionalLocalRootCoordinates (LocalIwahori)
open Arithmetic.ExceptionalMarkedRootDescent (markedFibreExists)

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 1600000 in
private theorem pinnedIwahoriComparison [FiniteDimensional k K] [IsGalois k K]
    [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    {E : BasedRootDatum.{u}} {M' : Model E} (c : MarkedCentralCover M M')
    (C' : MarkedFibre M' k)
    {l : Aut C.realization.attached.toBased ≃* Aut C.realization.pinned}
    {l' : Aut C'.realization.attached.toBased ≃* Aut C'.realization.pinned}
    {ω : Gal(K/k) →* Aut C.realization.attached.toBased}
    {ω' : Gal(K/k) →* Aut C'.realization.attached.toBased}
    (d : DescendedPair K (l := l) ω) (d' : DescendedPair K (l := l') ω')
    (σ : Gal(K/k)) (hd : Module.finrank k K = 2) (hσ : σ ≠ 1)
    (hf : let f := C.groupIso.inv ≫ (fibre k).map c.map ≫ C'.groupIso.hom
      f ≫ (pinnedDiagram d'.data σ).asIso.hom.group.hom =
        (pinnedDiagram d.data σ).asIso.hom.group.hom ≫ f)
    {W W' : Type u} [Group W] [Group W']
    {j : (𝟙_ (SchemeOver k) ⟶ d.group.val.X) →* IntegralPoints M.group (CommAlgCat.of Integers.{u} K)}
    {j' : (𝟙_ (SchemeOver k) ⟶ d'.group.val.X) →* IntegralPoints M'.group (CommAlgCat.of Integers.{u} K)}
    (hj : ∀ g, j g = pinnedGroundPoint C d.data g)
    (hj' : ∀ g, j' g = pinnedGroundPoint C' d'.data g)
    (P : LocalIwahori j W) (P' : LocalIwahori j' W')
    (p : (𝟙_ (SchemeOver k) ⟶ d.group.val.X) →* (𝟙_ (SchemeOver k) ⟶ d'.group.val.X))
    (hcomm : ∀ g, j' (p g) = integralPointHom c.map (CommAlgCat.of Integers.{u} K) (j g))
    (hnormal : p.range.Normal) :
    P'.iwahori.comap p = P.iwahori ∧
      ∀ h, h ∈ P'.iwahori ↔ ∃ (g : P.iwahori) (t : (integralUnitTorus (K := K) M').comap j'),
        h = p g * t := by
  classical
  let R := CommAlgCat.of Integers.{u} K
  let S := CommAlgCat.of Integers.{u} (valuation K).valuationSubring
  let i := valuationRingInclusion K
  let f := integralPointHom c.map R
  let L := markedBorelReduction M.group P.residueBorel
  let L' := markedBorelReduction M'.group P'.residueBorel
  let U' := (integralUnitTorus (K := K) M').comap j'
  let s := (pinnedDiagram d.data σ).asIso.hom
  let s' := (pinnedDiagram d'.data σ).asIso.hom
  let act := splitPointAction C s σ
  let act' := splitPointAction C' s' σ
  obtain ⟨F⟩ := markedFibreExists M K
  obtain ⟨F'⟩ := markedFibreExists M' K
  have hpre : L'.comap f = L :=
    splitIwahoriPreimage M M' c.map c.rootEquiv _ c.marking c.characterIndex
      (splitTorusPointPreimage c F F') P.residueFibre P'.residueFibre
      P.residueBorel P'.residueBorel P.borel_eq P'.borel_eq
  have hpreI : P'.iwahori.comap p = P.iwahori := by
    ext g
    change j' (p g) ∈ L' ↔ j g ∈ L
    rw [hcomm, ← hpre]
    rfl
  have hU : U' ≤ P'.iwahori :=
    Subgroup.comap_mono (reduction_contains_unitTorus P'.residueFibre P'.residueBorel P'.borel_eq)
  refine ⟨hpreI, ?_⟩
  intro g
  constructor
  · intro hg
    obtain ⟨ns, ps, hn, hp⟩ := positiveAndNegativeEnumerations D
    obtain ⟨hn', hp'⟩ := enumerates_map c.rootEquiv c.marking.1 ns ps hn hp
    let ns' := ns.map c.rootEquiv
    let ps' := ps.map c.rootEquiv
    let n := orderedRootPoint M.toIntegralMarking R ns
    let q := orderedRootPoint M.toIntegralMarking R ps
    obtain ⟨z, t, _, hcell⟩ :=
      (iwahoriDepthCoordinates P'.residueFibre P'.residueBorel P'.borel_eq ns' ps' hn' hp' (j' g)).mp hg
    let v : E.I → R := fun a => i.hom (z a)
    let x := v ∘ c.rootEquiv
    let u := (integralPointFunctor (splitTorus E)).map i (torusPoint E S t)
    have hcell' : f (n x) * ((u ≫ M'.torus.hom.hom : IntegralPoints M'.group R) * f (q x)) = j' g := by
      change (integralPointFunctor M'.group).map i
        (markedCellPoint M'.toIntegralMarking S ns' ps' z (torusPoint E S t)) = _ at hcell
      rw [markedCellPoint_map] at hcell
      rw [show f (n x) = orderedRootPoint M'.toIntegralMarking R ns' v from
          orderedRootPoint_image c.map c.rootEquiv R (c.marking.2.1 R) ns v,
        show f (q x) = orderedRootPoint M'.toIntegralMarking R ps' v from
          orderedRootPoint_image c.map c.rootEquiv R (c.marking.2.1 R) ps v]
      exact hcell
    have hgfix : act' (j' g) = j' g :=
      (splitPoint_fixed_iff C' d'.data σ hd hσ (j' g)).mp ⟨g, (hj' g).symm⟩
    obtain ⟨a, ha⟩ := stableSplitRoots C s σ ns false hn (g := n x) ⟨x, rfl⟩
    obtain ⟨b, hb⟩ := stableSplitRoots C s σ ps true hp (g := q x) ⟨x, rfl⟩
    obtain ⟨u', hu'⟩ := stableSplitTorus C' s' σ u
    let y : D.I → R := fun a₀ => if D.base.IsPos a₀ then b a₀ else a a₀
    have hyN : n y = act (n x) :=
      (orderedRootPoint_congr _ _ ns (fun a₀ h => ite_eq_right ((hn.2 a₀).mp h))).trans ha
    have hyP : q y = act (q x) :=
      (orderedRootPoint_congr _ _ ps (fun a₀ h => ite_eq_left ((hp.2 a₀).mp h))).trans hb
    have hy : f (n y) * ((u' ≫ M'.torus.hom.hom : IntegralPoints M'.group R) * f (q y)) =
        f (n x) * ((u ≫ M'.torus.hom.hom : IntegralPoints M'.group R) * f (q x)) := by
      rw [hyN, hyP, ← hu', ← splitAction_natural C C' c σ s s' hf (n x),
        ← splitAction_natural C C' c σ s s' hf (q x), ← act'.map_mul, ← act'.map_mul,
        hcell', hgfix]
    obtain ⟨hyx, _⟩ := centralCell_unique c R ns ps hn hp y x u' u hy
    have hnfix : act (n x) = n x := hyN.symm.trans (congrArg n hyx)
    have hpfix : act (q x) = q x := hyP.symm.trans (congrArg q hyx)
    obtain ⟨gN, hgN⟩ := (splitPoint_fixed_iff C d.data σ hd hσ _).mpr hnfix
    obtain ⟨gP, hgP⟩ := (splitPoint_fixed_iff C d.data σ hd hσ _).mpr hpfix
    have hN : j' (p gN) = f (n x) := (hcomm gN).trans (congrArg f ((hj gN).trans hgN))
    have hP : j' (p gP) = f (q x) := (hcomm gP).trans (congrArg f ((hj gP).trans hgP))
    have hparts : f (n x) ∈ L' ∧ (u ≫ M'.torus.hom.hom) ∈ integralUnitTorus (K := K) M' ∧
        f (q x) ∈ L' := by
      have hn₀ := orderedRootPoint_image c.map c.rootEquiv R (c.marking.2.1 R) ns v
      have hp₀ := orderedRootPoint_image c.map c.rootEquiv R (c.marking.2.1 R) ps v
      change f (n x) = _ at hn₀
      change f (q x) = _ at hp₀
      rw [hn₀, hp₀] at hcell' ⊢
      have hg' : j' g ∈ L' := hg
      exact iwahori_chart_factors P'.residueFibre P'.residueBorel P'.borel_eq ns' ps' hn' hp'
        v v u (hcell'.symm ▸ hg')
    have hNg : p gN ∈ P'.iwahori := show j' (p gN) ∈ L' by rw [hN]; exact hparts.1
    have hPg : p gP ∈ P'.iwahori := show j' (p gP) ∈ L' by rw [hP]; exact hparts.2.2
    let t₀ := (p gN)⁻¹ * g * (p gP)⁻¹
    have ht₀ : j' t₀ = u ≫ M'.torus.hom.hom := by
      change j' ((p gN)⁻¹ * g * (p gP)⁻¹) = _
      simp only [map_mul, map_inv, hN, hP]
      rw [← hcell']
      group
    have htU : t₀ ∈ U' := show j' t₀ ∈ _ from ht₀.symm ▸ hparts.2.1
    have htI : t₀ ∈ P'.iwahori := hU htU
    have hconj : t₀ * p gP * t₀⁻¹ ∈ p.range := hnormal.conj_mem _ ⟨gP, rfl⟩ _
    obtain ⟨a₀, ha₀⟩ := hconj
    have hmem : p (gN * a₀) ∈ P'.iwahori := by
      rw [map_mul, ha₀]
      exact P'.iwahori.mul_mem hNg
        (P'.iwahori.mul_mem (P'.iwahori.mul_mem htI hPg) (P'.iwahori.inv_mem htI))
    refine ⟨⟨gN * a₀, hpreI ▸ (show gN * a₀ ∈ P'.iwahori.comap p from hmem)⟩, ⟨t₀, htU⟩, ?_⟩
    change g = p (gN * a₀) * t₀
    rw [map_mul, ha₀]
    dsimp only [t₀]
    group
  · rintro ⟨a, t, rfl⟩
    have ha : a.val ∈ P'.iwahori.comap p := hpreI.symm ▸ a.property
    exact P'.iwahori.mul_mem ha (hU t.property)

end SplitFactors

open Specs.ExceptionalValuedTorusNormalizer (fixedWeylGroup markedDiagramEquiv)
open Arithmetic.ExceptionalValuedTorusNormalizer (markedFibreNormalizer)

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 1600000 in
/-- Compare the actual local subgroups and the finite and translation labels of a pinned cover. -/
theorem pinnedCentralLocalComparison : LocalComparison.{u} := by
  intro k K _ _ _ _ _ _ _ _ D E M M' c C C' l l' Q Q' ω ω' d d' σ hE hQ hQ' hd hσ
    _ _ τ τ' W W' hdiag R G H j j' hj'inj hj hj' P P' hN hN' hT hT' hw hw' hprod hprod' φ hφ
    N N' U U'
  obtain ⟨f, _, _, _, _, _, _, hpreT, hpreN, hnormal, _, hpoint⟩ :=
    pinnedCentralCoverComparison c hE C C' hQ hQ' d d' hd σ hσ hdiag
  let p := pointHom f (𝟙_ (SchemeOver k))
  have hmap (g : G) : j' (p g) = integralPointHom c.map R (j g) := by
    rw [hj', hj]
    exact hpoint g
  have heq : φ = p := MonoidHom.ext fun g => hj'inj ((hφ g).trans (hmap g).symm)
  subst φ
  have ht : N'.torus.comap p = N.torus := by
    ext g
    exact (hT' (p g)).trans ((hpreT g).trans (hT g).symm)
  have hn : N'.normalizer.comap p = N.normalizer := by
    ext g
    exact (hN' (p g)).trans ((hpreN g).trans (hN g).symm)
  have hEq := centralCover_diagramEquivariant c hE C C' hQ hQ' (d.data.outer σ) (d'.data.outer σ) hdiag
  obtain ⟨hi, hprodI⟩ := pinnedIwahoriComparison C c C' d d' σ hd hσ hEq hj hj' P P' p hmap hnormal
  refine ⟨hi, hprodI, hn, ht, integralUnit_preimage c N N' p hmap ht, hnormal, ?_⟩
  obtain ⟨e, he, _, hfixed⟩ := centralCoverWeylComparison c hE
  obtain ⟨eW, heW⟩ := hfixed τ τ' hdiag
  obtain ⟨F⟩ := markedFibreNormalizer K M'
  refine ⟨e, he, ?_⟩
  exact normalizerLabels c N N' p hmap F e he W.subtype W'.subtype eW heW hw hw' hprod hprod' ht

end

end LinearAlgebraicGroups.Arithmetic.ExceptionalPinnedCentralCover
