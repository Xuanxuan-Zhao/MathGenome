import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Arithmetic.ExceptionalPinnedPairCompatibility
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Affine.GroupSchemes
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Affine.ClosedSubgroups
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.ExceptionalIwahoriImageComparison
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Reductive.WeylScheme
import Batteries.Tactic.OpenPrivate

namespace LinearAlgebraicGroups.Arithmetic.ExceptionalPinnedPairCompatibility

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.MonoidalCategory
open scoped TensorProduct CategoryTheory.MonObj
open Specs.Pinning (BasedRootDatum)
open Specs.ExceptionalMarkedRootDescent
open Specs.IntegralSemisimpleModel
open Specs.ExceptionalIwahoriCongruence (changeRingHom integralRingMap)
open Specs.AdjointRepresentation (GroupPoints)
open Specs.Unipotent (closedSubgroupAlgebraicGroup)

universe u

attribute [local instance] integerAlgebra

section SubgroupPoints

open Specs.AdjointCocharacters (coordinateHopfIso coordinateHopfMap)
open Specs.AdjointBorelCohomology (PinnedTwist)
open Opposite
open private coordinatePresentation coordinatePointEquiv_comp restrictExtended_comp includeRight_injective
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.ExceptionalMarkedRootDescent
open private subgroupFactor from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Reductive.WeylScheme

variable {k K : Type u} [Field k] [Field K] [Algebra k K]

set_option backward.isDefEq.respectTransparency false in
private theorem coordinateHopfMap_surjective {G : AffineAlgebraicGroup k} (T : ClosedSubgroup G.val) :
    Function.Surjective
      (coordinateHopfMap (G := closedSubgroupAlgebraicGroup T) (H := G) T.inclusion).hom := by
  let r := coordinateHopfMap (G := closedSubgroupAlgebraicGroup T) (H := G) T.inclusion
  apply (hopfMapClosedImmersion k r).mp
  rw [coordinatePresentation (G := closedSubgroupAlgebraicGroup T) (H := G)]
  let U := Grp.forget (SchemeOver k) ⋙ Over.forget (Spec (CommRingCat.of k))
  let : IsClosedImmersion (U.map T.inclusion) := T.isClosedImmersion
  change IsClosedImmersion (U.map
    ((coordinateHopfIso (closedSubgroupAlgebraicGroup T)).hom ≫ T.inclusion ≫ (coordinateHopfIso G).inv))
  simp only [Functor.map_comp]
  infer_instance

private theorem algPoint_factors_of_extension {A B R S : Type u}
    [CommRing A] [CommRing B] [CommRing R] [CommRing S]
    [Algebra k A] [Algebra k B] [Algebra k R] [Algebra k S]
    (i : R →ₐ[k] S) (hi : Function.Injective i) (f : A →ₐ[k] B) (hf : Function.Surjective f)
    (p : A →ₐ[k] R) (q : B →ₐ[k] S) (h : i.comp p = q.comp f) :
    ∃ v : B →ₐ[k] R, v.comp f = p := by
  have hmem (x : B) : q x ∈ i.range := by
    obtain ⟨y, rfl⟩ := hf x
    exact ⟨p y, DFunLike.congr_fun h y⟩
  let e := AlgEquiv.ofInjective i hi
  let v := e.symm.toAlgHom.comp (q.codRestrict i.range hmem)
  refine ⟨v, ?_⟩
  apply AlgHom.ext
  intro y
  apply hi
  exact (congrArg Subtype.val (e.apply_symm_apply ⟨q (f y), hmem (f y)⟩)).trans
    (DFunLike.congr_fun h y).symm

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 450000 in
/-- Test-algebra points factor through a closed subgroup exactly when the
split comparison point factors through the corresponding split subgroup. -/
private theorem pinnedPoint_subgroup_iff
    {A : Specs.RootGroups.AdditiveLine k} {P : Specs.Pinning.PinnedGroup A}
    {D : Specs.Pinning.AttachedDatum P.pair} {l : Aut D.toBased ≃* Aut P}
    {G : AffineAlgebraicGroup k} {B T : ClosedSubgroup G.val}
    (d : PinnedTwist K D l B T)
    (U : ClosedSubgroup G.val) (U₀ : ClosedSubgroup P.pair.G.val)
    (a : extendedHopf K (Specs.AdjointCocharacters.coordinateHopf (closedSubgroupAlgebraicGroup U₀)) ≅
      extendedHopf K (Specs.AdjointCocharacters.coordinateHopf (closedSubgroupAlgebraicGroup U)))
    (h : d.groupIso.hom ≫ extendedHopfMap K (coordinateHopfMap
      (G := closedSubgroupAlgebraicGroup U) (H := G) U.inclusion) =
      extendedHopfMap K (coordinateHopfMap
        (G := closedSubgroupAlgebraicGroup U₀) (H := P.pair.G) U₀.inclusion) ≫ a.hom)
    (R : TestAlgebra k) (p : GroupPoints G.val R) :
    (∃ u : GroupPoints U.group R, u ≫ U.inclusion.hom.hom = p) ↔
      ∃ u : GroupPoints U₀.group ((extendedTestAlgebra k K).obj R),
        u ≫ U₀.inclusion.hom.hom = pinnedSchemePoint d R ((coordinatePointEquiv G R).symm p) := by
  let H := closedSubgroupAlgebraicGroup U
  let H₀ := closedSubgroupAlgebraicGroup U₀
  let G₀ := P.pair.G
  let S := (extendedTestAlgebra k K).obj R
  let φ := coordinateHopfMap (G := H) (H := G) U.inclusion
  let φ₀ := coordinateHopfMap (G := H₀) (H := G₀) U₀.inclusion
  let ψ := extendedHopfMap K φ
  let ψ₀ := extendedHopfMap K φ₀
  let q := ((coordinatePointEquiv G R).symm p).ofConv
  let qE := extendAlgebraPoint (K := K) q
  let g := d.groupIso.hom.hom.toAlgHom
  let f := a.hom.hom.toAlgHom
  let restrict (J : HopfAlgebraCategory k) :=
    (AlgHom.liftEquiv k K J (K ⊗[k] R)).symm
  have hq : coordinatePointEquiv G R (WithConv.toConv q) = p :=
    (coordinatePointEquiv G R).apply_symm_apply p
  have hsplit :
      pinnedSchemePoint d R ((coordinatePointEquiv G R).symm p) =
        coordinatePointEquiv G₀ S (WithConv.toConv (restrict _ (qE.comp g))) := rfl
  have comm (w : extendedHopf K (Specs.AdjointCocharacters.coordinateHopf H) →ₐ[K] (K ⊗[k] R)) :
      (w.comp ψ.hom.toAlgHom).comp g = (w.comp f).comp ψ₀.hom.toAlgHom := by
    apply AlgHom.ext
    intro x
    exact congrArg w (ConcreteCategory.congr_hom h x)
  constructor
  · rintro ⟨u, hu⟩
    let v := (coordinatePointEquiv H R).symm u
    have hv : v.ofConv.comp φ.hom.toAlgHom = q := by
      apply WithConv.toConv_injective
      apply (coordinatePointEquiv G R).injective
      rw [coordinatePointEquiv_comp (G := H) (H := G), hq, MulEquiv.apply_symm_apply, hu]
    let w := extendAlgebraPoint (K := K) v.ofConv
    have hw : w.comp ψ.hom.toAlgHom = qE := by
      apply (restrict (Specs.AdjointCocharacters.coordinateHopf G)).injective
      rw [restrictExtended_comp]
      change (restrict _ w).comp φ.hom.toAlgHom = restrict _ qE
      dsimp only [restrict, w, qE, extendAlgebraPoint]
      rw [Equiv.symm_apply_apply, Equiv.symm_apply_apply, AlgHom.comp_assoc, hv]
    refine ⟨coordinatePointEquiv H₀ S (WithConv.toConv (restrict _ (w.comp f))), ?_⟩
    rw [hsplit, ← hw, comm]
    change _ = coordinatePointEquiv G₀ S
      (WithConv.toConv ((AlgHom.liftEquiv k K (Specs.AdjointCocharacters.coordinateHopf G₀) (K ⊗[k] R)).symm
        ((w.comp f).comp ψ₀.hom.toAlgHom)))
    rw [restrictExtended_comp]
    exact (coordinatePointEquiv_comp (G := H₀) (H := G₀) U₀.inclusion S
      (WithConv.toConv (restrict _ (w.comp f)))).symm
  · rintro ⟨u, hu⟩
    let v := (coordinatePointEquiv H₀ S).symm u
    let vE := AlgHom.liftEquiv k K (Specs.AdjointCocharacters.coordinateHopf H₀) (K ⊗[k] R) v.ofConv
    have hv : vE.comp ψ₀.hom.toAlgHom = qE.comp g := by
      apply (restrict (Specs.AdjointCocharacters.coordinateHopf G₀)).injective
      change (AlgHom.liftEquiv k K (Specs.AdjointCocharacters.coordinateHopf G₀) (K ⊗[k] R)).symm
        (vE.comp ψ₀.hom.toAlgHom) = _
      rw [restrictExtended_comp]
      dsimp only [vE]
      rw [Equiv.symm_apply_apply]
      apply WithConv.toConv_injective
      apply (coordinatePointEquiv G₀ S).injective
      rw [coordinatePointEquiv_comp (G := H₀) (H := G₀), MulEquiv.apply_symm_apply, hu, hsplit]
    let w := vE.comp a.inv.hom.toAlgHom
    have hw : w.comp f = vE := by
      apply AlgHom.ext
      intro x
      exact congrArg vE (ConcreteCategory.congr_hom a.hom_inv_id x)
    have hwE : w.comp ψ.hom.toAlgHom = qE := by
      apply AlgHom.ext
      intro x
      obtain ⟨y, rfl⟩ := (ConcreteCategory.bijective_of_isIso d.groupIso.hom).surjective x
      exact DFunLike.congr_fun ((comm w).trans (by rw [hw, hv])) y
    have hw₀ := congrArg (restrict (Specs.AdjointCocharacters.coordinateHopf G)) hwE
    change (AlgHom.liftEquiv k K (Specs.AdjointCocharacters.coordinateHopf G) (K ⊗[k] R)).symm
      (w.comp (extendedHopfMap K φ).hom.toAlgHom) = _ at hw₀
    rw [restrictExtended_comp] at hw₀
    let j : R →ₐ[k] K ⊗[k] R := Algebra.TensorProduct.includeRight
    have hx : j.comp q = (restrict _ w).comp φ.hom.toAlgHom :=
      (Equiv.symm_apply_apply _ _).symm.trans hw₀.symm
    obtain ⟨b, hb⟩ := algPoint_factors_of_extension j includeRight_injective φ.hom.toAlgHom
      (coordinateHopfMap_surjective U) q (restrict _ w) hx
    refine ⟨coordinatePointEquiv H R (WithConv.toConv b), ?_⟩
    rw [← coordinatePointEquiv_comp (G := H) (H := G), hb, hq]

set_option backward.isDefEq.respectTransparency false in
private theorem subgroupFactor_of_points {G A : AffineAlgebraicGroup k} (T : ClosedSubgroup G.val)
    (f : A.val ⟶ G.val)
    (h : ∀ (R : TestAlgebra k) (p : GroupPoints A.val R),
      ∃ q : GroupPoints T.group R, q ≫ T.inclusion.hom.hom = p ≫ f.hom.hom) :
    ∃ j : A.val ⟶ T.group, j ≫ T.inclusion = f := by
  obtain ⟨R, ⟨u⟩⟩ := essImage_algSpec.mpr A.property.1
  obtain ⟨q, hq⟩ := h R.unop u.hom
  apply subgroupFactor T f (u.inv ≫ q)
  rw [Category.assoc, hq, Iso.inv_hom_id_assoc]

set_option backward.isDefEq.respectTransparency false in
private theorem subgroupIso_of_pointwise {G H : AffineAlgebraicGroup k}
    (U : ClosedSubgroup G.val) (T : ClosedSubgroup H.val) (j : G.val ≅ H.val)
    (h : ∀ (R : TestAlgebra k) (p : GroupPoints G.val R),
      (∃ q : GroupPoints U.group R, q ≫ U.inclusion.hom.hom = p) ↔
      ∃ q : GroupPoints T.group R, q ≫ T.inclusion.hom.hom = p ≫ j.hom.hom.hom) :
    ∃ i : U.group ≅ T.group, U.inclusion ≫ j.hom = i.hom ≫ T.inclusion := by
  let U₀ := closedSubgroupAlgebraicGroup U
  let T₀ := closedSubgroupAlgebraicGroup T
  obtain ⟨f, hf⟩ := subgroupFactor_of_points (A := U₀) T (U.inclusion ≫ j.hom)
    (fun R p => by
      simpa only [Grp.comp_hom_hom, Category.assoc] using
        (h R (p ≫ U.inclusion.hom.hom)).mp ⟨p, rfl⟩)
  have hj (R : TestAlgebra k) (q : GroupPoints T.group R) :
      (q ≫ T.inclusion.hom.hom ≫ j.inv.hom.hom) ≫ j.hom.hom.hom = q ≫ T.inclusion.hom.hom := by
    have hv : j.inv.hom.hom ≫ j.hom.hom.hom = 𝟙 _ := by
      exact congrArg (fun v => v.hom.hom) j.inv_hom_id
    rw [Category.assoc, Category.assoc, hv, Category.comp_id]
  obtain ⟨g, hg⟩ := subgroupFactor_of_points (A := T₀) U (T.inclusion ≫ j.inv)
    (fun R q => (h R _).mpr ⟨q, (hj R q).symm⟩)
  let : IsClosedImmersion U.inclusion.hom.hom.left := U.isClosedImmersion
  let : IsClosedImmersion T.inclusion.hom.hom.left := T.isClosedImmersion
  let : Mono U.inclusion.hom.hom := Over.mono_of_mono_left _
  let : Mono T.inclusion.hom.hom := Over.mono_of_mono_left _
  let : Mono U.inclusion := (Grp.forget (SchemeOver k)).mono_of_mono_map (by assumption)
  let : Mono T.inclusion := (Grp.forget (SchemeOver k)).mono_of_mono_map (by assumption)
  refine ⟨⟨f, g, ?_, ?_⟩, hf.symm⟩
  · apply (cancel_mono U.inclusion).mp
    simp only [Category.assoc, hg, ← Category.assoc f T.inclusion j.inv, hf,
      Category.assoc, j.hom_inv_id, Category.comp_id, Category.id_comp]
  · apply (cancel_mono T.inclusion).mp
    simp only [Category.assoc, hf, ← Category.assoc g U.inclusion j.hom, hg,
      Category.assoc, j.inv_hom_id, Category.comp_id, Category.id_comp]

end SubgroupPoints

section PairSubgroups

open Specs.AdjointBorelCohomology (PinnedTwist)
open Specs.ExceptionalIwahoriImageComparison (markedPositiveBorel)
open LinearAlgebraicGroups.Arithmetic.ExceptionalIwahoriImageComparison (markedPositiveBorelCoordinates)
open private fibrePointEquiv markedTorusEquiv markedTorusIncl markedTorusPoint_map
  orderedRootPoint_map from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.ExceptionalMarkedRootDescent
private theorem changeRingHom_comp_apply (I : IntegralGroup.{u})
    {R S U : IntegralAlgebra.{u}} (f : R ⟶ S) (g : S ⟶ U) (x : IntegralPoints I R) :
    changeRingHom I g (changeRingHom I f x) = changeRingHom I (f ≫ g) x := by
  exact (ConcreteCategory.congr_hom ((integralPointFunctor I).map_comp f g) x).symm

private def integralTorusPoints {D : BasedRootDatum.{u}} (M : IntegralMarking D) (S : IntegralAlgebra.{u}) :
    Set (IntegralPoints M.group S) :=
  Set.range (fun t : IntegralPoints (splitTorus D) S => t ≫ M.torus.hom.hom)

private def integralPositiveBorelPoints {D : BasedRootDatum.{u}} (M : IntegralMarking D)
    (S : IntegralAlgebra.{u}) (r : List D.I) : Set (IntegralPoints M.group S) :=
  Set.range (fun tv : IntegralPoints (splitTorus D) S × (D.I → S) =>
    (tv.1 ≫ M.torus.hom.hom) * orderedRootPoint M S r tv.2)

private theorem point_mem_iff_of_iso {I : IntegralGroup.{u}}
    (P : (S : IntegralAlgebra.{u}) → Set (IntegralPoints I S))
    (hf : ∀ {S U : IntegralAlgebra.{u}} (f : S ⟶ U) (x : IntegralPoints I S),
      x ∈ P S → changeRingHom I f x ∈ P U)
    {S U : IntegralAlgebra.{u}} (i : S ≅ U) (x : IntegralPoints I S) :
    changeRingHom I i.hom x ∈ P U ↔ x ∈ P S := by
  refine ⟨fun h => ?_, hf i.hom x⟩
  have h' := hf i.inv _ h
  rw [changeRingHom_comp_apply, i.hom_inv_id] at h'
  have hid : changeRingHom I (𝟙 S) x = x :=
    ConcreteCategory.congr_hom ((integralPointFunctor I).map_id S) x
  rwa [hid] at h'

private theorem integralTorusPoints_natural {D : BasedRootDatum.{u}} (M : IntegralMarking D)
    {S U : IntegralAlgebra.{u}} (f : S ⟶ U) (x : IntegralPoints M.group S)
    (hx : x ∈ integralTorusPoints M S) :
    changeRingHom M.group f x ∈ integralTorusPoints M U := by
  obtain ⟨t, rfl⟩ := hx
  exact ⟨(integralPointFunctor (splitTorus D)).map f t, (markedTorusPoint_map M f t).symm⟩

private theorem integralPositiveBorelPoints_natural {D : BasedRootDatum.{u}} (M : IntegralMarking D)
    (r : List D.I) {S U : IntegralAlgebra.{u}} (f : S ⟶ U) (x : IntegralPoints M.group S)
    (hx : x ∈ integralPositiveBorelPoints M S r) :
    changeRingHom M.group f x ∈ integralPositiveBorelPoints M U r := by
  obtain ⟨⟨t, v⟩, rfl⟩ := hx
  refine ⟨⟨(integralPointFunctor (splitTorus D)).map f t, fun a => f.hom (v a)⟩, ?_⟩
  change _ = changeRingHom M.group f ((t ≫ M.torus.hom.hom) * orderedRootPoint M S r v)
  rw [map_mul]
  exact congrArg₂ (· * ·) (markedTorusPoint_map M f t).symm (orderedRootPoint_map M f r v).symm

variable {k K : Type u} [Field k] [Field K] [Algebra k K]
    {D : BasedRootDatum.{u}} {M : Model D} (C : MarkedFibre M k)
    {l : Aut C.realization.attached.toBased ≃* Aut C.realization.pinned}
    {G : AffineAlgebraicGroup k} {B T : ClosedSubgroup G.val}
    (d : PinnedTwist K C.realization.attached l B T)

set_option backward.isDefEq.respectTransparency false in
private theorem pinnedPoint_torus_iff (R : TestAlgebra k) (p : GroupPoints G.val R) :
    (∃ t : GroupPoints T.group R, t ≫ T.inclusion.hom.hom = p) ↔
      pinnedMarkedPoint C d R ((coordinatePointEquiv G R).symm p) ∈
        integralTorusPoints M.toIntegralMarking ((quadraticIntegralAlgebra k K).obj R) := by
  let S := (extendedTestAlgebra k K).obj R
  let T₀ := C.realization.pinned.pair.T
  rw [pinnedPoint_subgroup_iff d T T₀ d.torusIso d.torusComm]
  constructor
  · rintro ⟨t, ht⟩
    refine ⟨markedTorusEquiv C S t, ?_⟩
    exact (markedTorusIncl C S t).symm.trans (congrArg (markedFibrePoint C S) ht)
  · rintro ⟨u, hu⟩
    obtain ⟨t, ht⟩ := (markedTorusEquiv C S).surjective u
    refine ⟨t, (fibrePointEquiv C S).injective ?_⟩
    change markedFibrePoint C S (t ≫ T₀.inclusion.hom.hom) =
      pinnedMarkedPoint C d R ((coordinatePointEquiv G R).symm p)
    rw [markedTorusIncl, ht]
    exact hu

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 600000 in
private theorem pinnedPoint_borel_iff (R : TestAlgebra k) (p : GroupPoints G.val R)
    (r : List D.I) (hr : Specs.OrderedRootProducts.Enumerates r {a | D.base.IsPos a}) :
    (∃ b : GroupPoints B.group R, b ≫ B.inclusion.hom.hom = p) ↔
      pinnedMarkedPoint C d R ((coordinatePointEquiv G R).symm p) ∈
        integralPositiveBorelPoints M.toIntegralMarking ((quadraticIntegralAlgebra k K).obj R) r := by
  let S := (extendedTestAlgebra k K).obj R
  let B₀ := C.realization.pinned.pair.B
  let q := pinnedSchemePoint d R ((coordinatePointEquiv G R).symm p)
  have hcoords : markedPositiveBorel C S =
      integralPositiveBorelPoints M.toIntegralMarking ((quadraticIntegralAlgebra k K).obj R) r :=
    markedPositiveBorelCoordinates C S r hr
  change _ ↔ markedFibrePoint C S q ∈
    integralPositiveBorelPoints M.toIntegralMarking ((quadraticIntegralAlgebra k K).obj R) r
  rw [← hcoords]
  refine (pinnedPoint_subgroup_iff d B B₀ d.borelIso d.borelComm R p).trans ?_
  have hmark (b : GroupPoints B₀.group S) :
      forgetFibrePoint M.group S (b ≫ B₀.inclusion.hom.hom ≫ C.groupIso.inv.hom.hom) =
        markedFibrePoint C S (b ≫ B₀.inclusion.hom.hom) := by
    unfold markedFibrePoint
    rw [Category.assoc]
  change (∃ b : GroupPoints B₀.group S, b ≫ B₀.inclusion.hom.hom = q) ↔
    ∃ b : GroupPoints B₀.group S,
      forgetFibrePoint M.group S (b ≫ B₀.inclusion.hom.hom ≫ C.groupIso.inv.hom.hom) =
        markedFibrePoint C S q
  constructor
  · rintro ⟨b, hb⟩
    exact ⟨b, (hmark b).trans (congrArg (markedFibrePoint C S) hb)⟩
  · rintro ⟨b, hb⟩
    exact ⟨b, (fibrePointEquiv C S).injective ((hmark b).symm.trans hb)⟩

set_option backward.isDefEq.respectTransparency false in
private theorem baseChange_subgroupPoint_iff {F k : Type u} [Field F] [Field k] [Algebra F k]
    {G : AffineAlgebraicGroup F} (T : ClosedSubgroup G.val) (R : TestAlgebra k)
    (p : GroupPoints ((groupBaseChange F k).obj G.val) R) :
    (∃ t : GroupPoints ((groupBaseChange F k).obj T.group) R,
      t ≫ ((groupBaseChange F k).map T.inclusion).hom.hom = p) ↔
    ∃ t : GroupPoints T.group ((restrictTestAlgebra F k).obj R),
      t ≫ T.inclusion.hom.hom = baseChangePoint F k G.val.X R p := by
  have hn (t : GroupPoints ((groupBaseChange F k).obj T.group) R) :
      baseChangePoint F k G.val.X R (t ≫ ((groupBaseChange F k).map T.inclusion).hom.hom) =
        (baseChangePoint F k T.group.X R t) ≫ T.inclusion.hom.hom :=
    baseChangePointsSchemeNaturality F k T.inclusion.hom.hom R t
  constructor
  · rintro ⟨t, rfl⟩
    exact ⟨baseChangePoint F k T.group.X R t, (hn t).symm⟩
  · rintro ⟨q, hq⟩
    obtain ⟨t, rfl⟩ := (baseChangePoints F k T.group.X R).surjective q
    exact ⟨t, (baseChangePoints F k G.val.X R).injective ((hn t).trans hq)⟩

end PairSubgroups

section GroundEvaluation

open Specs.ExceptionalIwahoriImageComparison (pinnedGroundPoint)
open private coordinatePointEquiv_natural from
  MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.ExceptionalMarkedRootDescent

variable {F L k K : Type u} [Field F] [Field L] [Field k] [Field K]
  [Algebra F L] [Algebra F k] [Algebra F K] [Algebra k K]

private def coefficientGroundMap : (restrictTestAlgebra F k).obj (CommAlgCat.of k k) ⟶
    CommAlgCat.of F k :=
  (CommAlgCat.homEquivCommRingCat (R := F) _ _).symm ⟨𝟙 _, RingHom.ext (fun _ => rfl)⟩

set_option backward.isDefEq.respectTransparency false in
private theorem coefficientGroundMap_points {F k : Type u} [Field F] [Field k] [Algebra F k]
    {G : SchemeOver F} (p : Points G ((restrictTestAlgebra F k).obj (CommAlgCat.of k k))) :
    mapPoints (coefficientGroundMap (F := F) (k := k)) p = p := by
  apply Over.OverMorphism.ext
  change Spec.map (𝟙 (CommRingCat.of k)) ≫ p.left = p.left
  rw [Spec.map_id, Category.id_comp]

open Algebra.TensorProduct

set_option backward.isDefEq.respectTransparency false in
private theorem coefficientTensor_ground
    (e : (L ⊗[F] k) ≃ₐ[F] K)
    (he : ∀ y : k, e ((1 : L) ⊗ₜ[F] y) = algebraMap k K y)
    (c : restrictTestAlgebra F k ⋙ quadraticIntegralAlgebra F L ≅ quadraticIntegralAlgebra k K)
    (hc : ∀ (z : L) (y : k),
      (c.hom.app (CommAlgCat.of k k)).hom
        (@TensorProduct.tmul F _ L ((restrictTestAlgebra F k).obj (CommAlgCat.of k k)) _ _ _
            ((restrictTestAlgebra F k).obj (CommAlgCat.of k k)).algebra.toModule z y) =
        (e (z ⊗ₜ[F] (1 : k))) ⊗ₜ[k] y) :
    c.hom.app (CommAlgCat.of k k) ≫ evaluateGroundTensor k K =
      (quadraticIntegralAlgebra F L).map (coefficientGroundMap (F := F) (k := k)) ≫
        integralRingMap e.toRingHom := by
  apply CommAlgCat.hom_ext
  apply AlgHom.ext
  let R₀ := (restrictTestAlgebra F k).obj (CommAlgCat.of k k)
  let R := CommAlgCat.of F k
  let f : R₀ ⟶ R := coefficientGroundMap
  let left := (evaluateGroundTensor k K).hom.comp (c.hom.app (CommAlgCat.of k k)).hom
  let right := (integralRingMap e.toRingHom).hom.comp ((quadraticIntegralAlgebra F L).map f).hom
  change ∀ x : @TensorProduct F _ L R₀ _ _ _ R₀.algebra.toModule, left x = right x
  intro x
  induction x using TensorProduct.inductionOn with
  | add x y hx hy => rw [map_add, map_add, hx, hy]
  | tmul z y =>
    change (Algebra.TensorProduct.rid k K K)
      ((c.hom.app (CommAlgCat.of k k)).hom
        (@TensorProduct.tmul F _ L R₀ _ _ _ R₀.algebra.toModule z y)) =
      e (z ⊗ₜ[F] (y : k))
    rw [hc z y, rid_tmul]
    rw [Algebra.smul_def, ← he y, ← map_mul, tmul_mul_tmul, one_mul, mul_one]

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 400000 in
private theorem pinnedMarkedPoint_mapPoints {k K : Type u} [Field k] [Field K] [Algebra k K]
    [FiniteDimensional k K] [IsGalois k K]
    {D : BasedRootDatum.{u}} {M : Model D} (C : MarkedFibre M k)
    {l : Aut C.realization.attached.toBased ≃* Aut C.realization.pinned}
    {G : AffineAlgebraicGroup k} {B T : ClosedSubgroup G.val}
    (d : Specs.AdjointBorelCohomology.PinnedTwist K C.realization.attached l B T)
    {R S : TestAlgebra k} (f : R ⟶ S) (p : GroupPoints G.val R) :
    changeRingHom M.group ((quadraticIntegralAlgebra k K).map f)
        (pinnedMarkedPoint C d R ((coordinatePointEquiv G R).symm p)) =
      pinnedMarkedPoint C d S ((coordinatePointEquiv G S).symm (mapPoints f p)) := by
  let v := (coordinatePointEquiv G R).symm p
  have hv : WithConv.toConv (f.hom.comp v.ofConv) =
      (coordinatePointEquiv G S).symm (mapPoints f p) := by
    apply (coordinatePointEquiv G S).injective
    rw [coordinatePointEquiv_natural, MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply]
  obtain ⟨i, hi, _⟩ :=
    LinearAlgebraicGroups.Arithmetic.ExceptionalMarkedRootDescent.pinnedMarkedPointEmbedding C d
  rw [← hv, ← hi R v, ← hi S (WithConv.toConv (f.hom.comp v.ofConv))]
  exact (ConcreteCategory.congr_hom (i.naturality f) v).symm

end GroundEvaluation

open private positiveAndNegativeEnumerations from
  MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.ExceptionalIwahoriImageComparison

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 1000000 in
theorem pinnedPairCompatibility : Specs.ExceptionalPinnedPairCompatibility.Statement.{u} := by
  intro F L k K _ _ _ _ _ _ _ _ _ _ _ _ _ D M C Ck l lk G Gk B T Bk Tk d dk e he c j hc hj
  let H := Specs.Unipotent.baseChangedAlgebraicGroup k G
  let b := restrictTestAlgebra F k
  let β := groupBaseChange F k
  let Ub := Specs.GeometricRadicals.baseChangedSubgroup k B
    (baseChangeClosedSubgroup F k B.inclusion B.isClosedImmersion)
  let Ut := Specs.GeometricRadicals.baseChangedSubgroup k T
    (baseChangeClosedSubgroup F k T.inclusion T.isClosedImmersion)
  obtain ⟨_, r, _, hr⟩ := positiveAndNegativeEnumerations D
  have hB (R : TestAlgebra k) (p : GroupPoints Gk.val R) :
      (∃ q : GroupPoints Bk.group R, q ≫ Bk.inclusion.hom.hom = p) ↔
      ∃ q : GroupPoints Ub.group R, q ≫ Ub.inclusion.hom.hom = p ≫ j.hom.hom.hom := by
    change _ ↔ ∃ q : GroupPoints (β.obj B.group) R,
      q ≫ (β.map B.inclusion).hom.hom = p ≫ j.hom.hom.hom
    rw [baseChange_subgroupPoint_iff, pinnedPoint_borel_iff Ck dk R p r hr,
      pinnedPoint_borel_iff C d (b.obj R) _ r hr, hj]
    exact point_mem_iff_of_iso (fun S => integralPositiveBorelPoints M.toIntegralMarking S r)
      (integralPositiveBorelPoints_natural M.toIntegralMarking r) (c.app R) _
  have hT (R : TestAlgebra k) (p : GroupPoints Gk.val R) :
      (∃ q : GroupPoints Tk.group R, q ≫ Tk.inclusion.hom.hom = p) ↔
      ∃ q : GroupPoints Ut.group R, q ≫ Ut.inclusion.hom.hom = p ≫ j.hom.hom.hom := by
    change _ ↔ ∃ q : GroupPoints (β.obj T.group) R,
      q ≫ (β.map T.inclusion).hom.hom = p ≫ j.hom.hom.hom
    rw [baseChange_subgroupPoint_iff, pinnedPoint_torus_iff Ck dk R p,
      pinnedPoint_torus_iff C d (b.obj R), hj]
    exact point_mem_iff_of_iso (integralTorusPoints M.toIntegralMarking)
      (integralTorusPoints_natural M.toIntegralMarking) (c.app R) _
  obtain ⟨jB, hjB⟩ := subgroupIso_of_pointwise (G := Gk) (H := H) Bk Ub j hB
  obtain ⟨jT, hjT⟩ := subgroupIso_of_pointwise (G := Gk) (H := H) Tk Ut j hT
  refine ⟨jB, jT, hjB, hjT, fun g => ?_⟩
  let R := CommAlgCat.of k k
  let R₀ := b.obj R
  let f := coefficientGroundMap (F := F) (k := k)
  let p : GroupPoints Gk.val R :=
    CartesianMonoidalCategory.toUnit ((testSpec k).obj (Opposite.op R)) ≫ g
  let q := baseChangePoint F k G.val.X R (p ≫ j.hom.hom.hom)
  change changeRingHom M.group (evaluateGroundTensor k K)
    (pinnedMarkedPoint Ck dk R ((coordinatePointEquiv Gk R).symm p)) = _
  rw [hj R p, changeRingHom_comp_apply, coefficientTensor_ground e he c (hc R),
    ← changeRingHom_comp_apply]
  change changeRingHom M.group (integralRingMap e.toRingHom)
    (changeRingHom M.group ((quadraticIntegralAlgebra F L).map f)
      (pinnedMarkedPoint C d R₀ ((coordinatePointEquiv G R₀).symm q))) = _
  rw [pinnedMarkedPoint_mapPoints C d f q, coefficientGroundMap_points q]
  dsimp only [q, p, R]
  rw [Category.assoc]

end

end LinearAlgebraicGroups.Arithmetic.ExceptionalPinnedPairCompatibility
