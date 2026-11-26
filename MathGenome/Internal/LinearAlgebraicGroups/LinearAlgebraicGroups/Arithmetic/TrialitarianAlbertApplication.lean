import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Arithmetic.TrialitarianAlbertApplication
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.SplitAlbertLocalForms
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.TrialitarianAlbertDescent
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.TrialitarianSplitTorus
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Descent.RelativeRank
import Mathlib.Algebra.Field.Shrink
import Mathlib.Algebra.Ring.Shrink
import Mathlib.Algebra.Polynomial.Laurent
import Mathlib.Logic.Small.Basic
import Batteries.Tactic.OpenPrivate

namespace LinearAlgebraicGroups.Arithmetic.TrialitarianAlbertApplication

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open LinearAlgebraicGroups.Specs
open TrialitarianAlbertDescentSpecification (AlbertModel DiagramPresentation CubicStabilizer)
open LinearAlgebraicGroups.Specs.Arithmetic.TrialitarianCliffordInvariants
open LinearAlgebraicGroups.Albert
open SplitSpecification (ParaQuadratic IsSplitModel)
open IntrinsicCubicSpecification (SplitChart)
open ReductiveFiberSpecification (SplitAction)
open TrialitySpecification (Model modelOp mapModel modelBaseChange)
open scoped CategoryTheory.MonObj TensorProduct

universe u v w

noncomputable section

set_option linter.style.haveILetI false
set_option synthInstance.maxHeartbeats 100000

open private modelBaseChange_tmul modelBaseChange_operator mapModel_unit
  extendChart extendChart_apply from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Albert.IntrinsicCubic
open private ground_operator from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Albert.QuadraticOperators
open private modelBaseChange_natural from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Albert.ShortDirections
open LowerRankSpecification (untwisted)
open LinearAlgebraicGroups.Composition (Zorn)
open LinearAlgebraicGroups.Composition.ZornSpecification (norm)

variable {F : Type u} [Field F]

/-- Ground coordinates coming from a split Albert law induce compatible
coordinates on each test algebra. -/
private theorem splitCharts (J : AlbertModel F)
    (hJ : IsSplitModel J.law .octonion) :
    ∃ c : ∀ R : TestAlgebra F, SplitChart J.law R,
      ∀ {R T : TestAlgebra F} (f : R ⟶ T) (x : R ⊗[F] J.V),
        mapModel f.hom.toRingHom ((c R).coordinates x) =
          (c T).coordinates (TensorProduct.map f.hom.toLinearMap LinearMap.id x) := by
  obtain ⟨e, hu, ho⟩ := hJ
  let K := ParaQuadratic.ofJordan (weightedHermitianJordan (untwisted F)
    (LinearAlgebraicGroups.Composition.Zorn.isOctonion F))
  have he : J.law.IsIso K e := (J.law.isIso_iff_ground K e).2 ⟨hu, fun x y =>
    (ho x y).trans (ground_operator (untwisted F)
      (LinearAlgebraicGroups.Composition.Zorn.isOctonion F) (e x) (e y)).symm⟩
  let t (R : TestAlgebra F) : R ⊗[F] J.V ≃ₗ[R] Model R :=
    (e.baseChange F R J.V (Model F)).trans (modelBaseChange F R)
  have ht (R : TestAlgebra F) (r : R) (x : J.V) :
      t R (r ⊗ₜ[F] x) = r • mapModel (algebraMap F R) (e x) := by
    change modelBaseChange F R (r ⊗ₜ[F] e x) = _
    exact modelBaseChange_tmul r (e x)
  refine ⟨fun R => ⟨t R, ?_, ?_⟩, ?_⟩
  · rw [ht, one_smul, hu]
    exact mapModel_unit _
  · intro x y
    change modelBaseChange F R (e.toLinearMap.baseChange R (J.law.op R x y)) = _
    rw [he.2 R]
    exact modelBaseChange_operator _ _
  · intro R T f x
    have hn := modelBaseChange_natural f.hom ((e.baseChange F R J.V (Model F)) x)
    refine hn.symm.trans (congrArg (modelBaseChange F T) ?_)
    clear hn
    induction x using TensorProduct.inductionOn with
    | tmul r x => rfl
    | add x y hx hy => simp only [map_add, hx, hy]

open IdempotentSpecification (IsSplitAutomorphism)

private def actionInCoordinates (J : AlbertModel F) (R : TestAlgebra F)
    (c : SplitChart J.law R) :
    Points J.automorphisms.val.X R →* (Model R ≃ₗ[R] Model R) :=
  { toFun := fun g => c.coordinates.symm.trans ((J.action R g).trans c.coordinates)
    map_one' := LinearEquiv.ext fun x => by
      rw [map_one]
      exact c.coordinates.apply_symm_apply x
    map_mul' := fun g h => LinearEquiv.ext fun x => by
      rw [map_mul]
      change c.coordinates (J.action R g (J.action R h (c.coordinates.symm x))) =
        c.coordinates (J.action R g (c.coordinates.symm
          (c.coordinates (J.action R h (c.coordinates.symm x)))))
      rw [LinearEquiv.symm_apply_apply] }

private theorem actionInCoordinates_apply (J : AlbertModel F) (R : TestAlgebra F)
    (c : SplitChart J.law R) (g : Points J.automorphisms.val.X R) (x : R ⊗[F] J.V) :
    actionInCoordinates J R c g (c.coordinates x) = c.coordinates (J.action R g x) := by
  change c.coordinates (J.action R g (c.coordinates.symm (c.coordinates x))) = _
  rw [LinearEquiv.symm_apply_apply]

private theorem actionInCoordinates_injective (J : AlbertModel F) (R : TestAlgebra F)
    (c : SplitChart J.law R) :
    Function.Injective (actionInCoordinates J R c) := by
  intro a b hab
  apply J.faithful R
  apply LinearEquiv.ext
  intro x
  apply c.coordinates.injective
  rw [← actionInCoordinates_apply J R c a, ← actionInCoordinates_apply J R c b, hab]

private theorem actionInCoordinates_image (J : AlbertModel F) (R : TestAlgebra F)
    (c : SplitChart J.law R) :
    Set.range (actionInCoordinates J R c) = {a | IsSplitAutomorphism a} := by
  ext a
  constructor
  · rintro ⟨g, rfl⟩
    have hg : J.action R g ∈ Set.range (J.action R) := ⟨g, rfl⟩
    rw [J.image R] at hg
    change J.action R g (1 ⊗ₜ[F] J.law.unit) = _ ∧
      ∀ x y, J.action R g (J.law.op R x y) =
        J.law.op R (J.action R g x) (J.action R g y) at hg
    change IsSplitAutomorphism (actionInCoordinates J R c g)
    refine ⟨?_, fun x y => ?_⟩
    · rw [← c.unit, actionInCoordinates_apply, hg.1]
    · obtain ⟨x, rfl⟩ := c.coordinates.surjective x
      obtain ⟨y, rfl⟩ := c.coordinates.surjective y
      have hop (x y : R ⊗[F] J.V) : c.coordinates (J.law.op R x y) =
          modelOp (c.coordinates x) (c.coordinates y) := c.op x y
      rw [← hop, actionInCoordinates_apply, hg.2, hop,
        actionInCoordinates_apply, actionInCoordinates_apply]
  · intro ha
    change IsSplitAutomorphism a at ha
    let b := c.coordinates.trans (a.trans c.coordinates.symm)
    have hb (x : R ⊗[F] J.V) : c.coordinates (b x) = a (c.coordinates x) :=
      c.coordinates.apply_symm_apply _
    have hm : b ∈ Set.range (J.action R) := by
      rw [J.image R]
      refine ⟨c.coordinates.injective ?_, fun x y => c.coordinates.injective ?_⟩
      · rw [hb, c.unit, ha.1]
      · rw [hb, c.op, c.op, hb, hb]
        exact ha.2 _ _
    obtain ⟨g, hg⟩ := hm
    refine ⟨g, LinearEquiv.ext fun x => ?_⟩
    obtain ⟨x, rfl⟩ := c.coordinates.surjective x
    rw [actionInCoordinates_apply, hg, hb]

private theorem actionInCoordinates_natural (J : AlbertModel F)
    (c : ∀ R : TestAlgebra F, SplitChart J.law R)
    (hc : ∀ {R T : TestAlgebra F} (f : R ⟶ T) (x : R ⊗[F] J.V),
      mapModel f.hom.toRingHom ((c R).coordinates x) =
        (c T).coordinates (TensorProduct.map f.hom.toLinearMap LinearMap.id x))
    {R T : TestAlgebra F} (f : R ⟶ T) (g : Points J.automorphisms.val.X R) (x : Model R) :
    mapModel f.hom.toRingHom (actionInCoordinates J R (c R) g x) =
      actionInCoordinates J T (c T) (mapPoints f g) (mapModel f.hom.toRingHom x) := by
  obtain ⟨x, rfl⟩ := (c R).coordinates.surjective x
  rw [actionInCoordinates_apply, hc, hc, actionInCoordinates_apply, J.natural]

open private positive_rank_iff_cocharacter proper_parabolic_cocharacter from
    MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Descent.RelativeRank

private def chartTransition (J : AlbertModel F) (R : TestAlgebra F)
    (c d : SplitChart J.law R) : Model R ≃ₗ[R] Model R :=
  c.coordinates.symm.trans d.coordinates

private theorem chartTransition_apply (J : AlbertModel F) (R : TestAlgebra F)
    (c d : SplitChart J.law R) (x : R ⊗[F] J.V) :
    chartTransition J R c d (c.coordinates x) = d.coordinates x :=
  congrArg d.coordinates (c.coordinates.symm_apply_apply x)

private theorem chartTransition_automorphism (J : AlbertModel F) (R : TestAlgebra F)
    (c d : SplitChart J.law R) : IsSplitAutomorphism (chartTransition J R c d) := by
  refine ⟨?_, fun x y => ?_⟩
  · calc
      chartTransition J R c d CubicSpecification.cubicUnit =
          d.coordinates (1 ⊗ₜ[F] J.law.unit) := by
        conv_lhs => rw [← c.unit]
        exact chartTransition_apply J R c d _
      _ = _ := d.unit
  · obtain ⟨x, rfl⟩ := c.coordinates.surjective x
    obtain ⟨y, rfl⟩ := c.coordinates.surjective y
    have hop (x y : R ⊗[F] J.V) : c.coordinates (J.law.op R x y) =
        modelOp (c.coordinates x) (c.coordinates y) := c.op x y
    have hdp (x y : R ⊗[F] J.V) : d.coordinates (J.law.op R x y) =
        modelOp (d.coordinates x) (d.coordinates y) := d.op x y
    rw [← hop, chartTransition_apply, hdp, chartTransition_apply, chartTransition_apply]

section LocalFields

open ValuativeRel TopologicalSpace Filter Set
open scoped Topology

private theorem smallOfSecondCountable (X : Type u) [TopologicalSpace X] [T2Space X]
    [SecondCountableTopology X] : Small.{0} X := by
  classical
  let B := countableBasis X
  letI : Encodable B := (countable_countableBasis X).toEncodable
  let f (x : X) : Set ℕ := {n | ∃ b : B, Encodable.encode b = n ∧ x ∈ b.val}
  refine small_of_injective (f := f) fun x y h => ?_
  by_contra hxy
  obtain ⟨U, V, hU, hV, hx, hy, hUV⟩ := t2_separation hxy
  obtain ⟨b, hb, hxb, hbU⟩ := (isBasis_countableBasis X).exists_subset_of_mem_open hx hU
  have hfx : Encodable.encode (⟨b, hb⟩ : B) ∈ f x := ⟨⟨b, hb⟩, rfl, hxb⟩
  rw [h] at hfx
  obtain ⟨b', henc, hyb⟩ := hfx
  have hh : b' = (⟨b, hb⟩ : B) := Encodable.encode_injective henc
  rw [hh] at hyb
  exact Set.disjoint_left.mp hUV (hbU hyb) hy
-- Adapted from Mathlib/NumberTheory/LocalField/Basic.lean (Nonarchimedean local field rank-one valuation setup). Copyright (c) 2025 Andrew Yang. All rights reserved. Released under Apache 2.0, see LICENSE. MathGenome adapts the rank-one valuation setup to the local-field smallness proof.
private theorem localFieldSmall (F : Type u) [Field F] [ValuativeRel F]
    [TopologicalSpace F] [IsNonarchimedeanLocalField F] : Small.{0} F := by
  letI := IsTopologicalAddGroup.rightUniformSpace F
  letI := isUniformAddGroup_of_addCommGroup (G := F)
  letI : (Valued.v (R := F)).RankOne :=
    { hom' := IsRankLeOne.nonempty.some.emb (R := F).comp MonoidWithZeroHom.ValueGroup₀.embedding
      strictMono' := IsRankLeOne.nonempty.some.strictMono.comp
        MonoidWithZeroHom.ValueGroup₀.embedding_strictMono }
  letI : NontriviallyNormedField F := Valued.toNontriviallyNormedField F (ValueGroupWithZero F)
  letI : ProperSpace F := .of_nontriviallyNormedField_of_weaklyLocallyCompactSpace F
  exact smallOfSecondCountable F

private theorem valuationNeighborhood {F : Type*} [Field F] [ValuativeRel F]
    [TopologicalSpace F] [IsValuativeTopology F] {s : Set F} {x : F} :
    s ∈ 𝓝 x ↔ ∃ r : F, r ≠ 0 ∧ {z | valuation F (z - x) < valuation F r} ⊆ s := by
  rw [IsValuativeTopology.mem_nhds_iff']
  constructor
  · rintro ⟨radius, hradius⟩
    obtain ⟨r, hr⟩ := ValuativeRel.valuation_surjective (radius : ValueGroupWithZero F)
    exact ⟨r, fun h => radius.ne_zero (by rw [← hr, h, map_zero]), by simpa only [hr] using hradius⟩
  · rintro ⟨r, hr, hsub⟩
    exact ⟨Units.mk0 (valuation F r) (map_ne_zero _ |>.mpr hr), hsub⟩

private theorem localFieldTransport {F : Type u} [Field F] [ValuativeRel F]
    [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    {k : Type*} [Field k] (e : k ≃+* F) :
    letI := TopologicalSpace.induced e ‹TopologicalSpace F›
    letI := ValuativeRel.ofValuation ((valuation F).comap e.toRingHom)
    IsNonarchimedeanLocalField k := by
  letI := TopologicalSpace.induced e ‹TopologicalSpace F›
  letI := ValuativeRel.ofValuation ((valuation F).comap e.toRingHom)
  let v := (valuation F).comap e.toRingHom
  haveI : v.Compatible := Valuation.Compatible.ofValuation v
  let h : k ≃ₜ F := e.toEquiv.toHomeomorphOfIsInducing ⟨rfl⟩
  haveI : LocallyCompactSpace k := h.isOpenEmbedding.locallyCompactSpace
  have hv : IsValuativeTopology k := by
    constructor
    intro s x
    have hs : s ∈ 𝓝 x ↔ h '' s ∈ 𝓝 (e x) := by
      change s ∈ 𝓝 x ↔ h '' s ∈ 𝓝 (h x)
      rw [← h.map_nhds_eq x, Filter.mem_map]
      simp only [h.preimage_image]
    rw [hs, valuationNeighborhood]
    have hball (radius : (ValueGroupWithZero k)ˣ) :
        (x + ·) '' { z | valuation k z < radius } =
          {z | valuation k (z - x) < radius} := by
      ext z
      constructor
      · rintro ⟨w, hw, rfl⟩
        simpa only [Set.mem_ofPred_eq, add_sub_cancel_left] using hw
      · intro hz
        exact ⟨z - x, hz, show x + (z - x) = z by rw [add_comm x, sub_add_cancel]⟩
    simp only [hball]
    constructor
    · rintro ⟨r, hr, hsub⟩
      refine ⟨Units.mk0 (valuation k (e.symm r)) ((map_ne_zero _).mpr (fun he => hr (e.symm.injective (he.trans (map_zero e.symm).symm)))), ?_⟩
      intro z hz
      suffices e z ∈ h '' s from by
        change z ∈ h ⁻¹' (h '' s) at this
        rwa [h.preimage_image] at this
      apply hsub
      change valuation F (e z - e x) < valuation F r
      rw [← map_sub e, ← e.apply_symm_apply r]
      exact (v.vlt_iff_lt).mp ((valuation k).vlt_iff_lt.mpr hz)
    · rintro ⟨radius, hsub⟩
      obtain ⟨r, hr⟩ := ValuativeRel.valuation_surjective (radius : ValueGroupWithZero k)
      refine ⟨e r, fun he => radius.ne_zero (by rw [← hr, show r = 0 by simpa using he, map_zero]), ?_⟩
      intro z hz
      obtain ⟨z, rfl⟩ := e.surjective z
      refine ⟨z, hsub ?_, rfl⟩
      change valuation k (z - x) < (radius : ValueGroupWithZero k)
      rw [← hr]
      apply (valuation k).vlt_iff_lt.mp
      apply (v.vlt_iff_lt).mpr
      change valuation F (e (z - x)) < valuation F (e r)
      rw [map_sub]
      exact hz
  have hnt : ValuativeRel.IsNontrivial k := by
    apply (ValuativeRel.isNontrivial_iff_isNontrivial v).mpr
    obtain ⟨x, hx, hlt⟩ := Valuation.IsNontrivial.exists_lt_one (v := valuation F)
    exact ⟨e.symm x, by simpa [v] using hx, by simpa [v] using hlt.ne⟩
  exact ⟨⟩

end LocalFields

section ScalarCoordinates

open LinearAlgebraicGroups.Composition.ZornSpecification (mapCoordinates)
open private map_octonion_add map_octonion_smul map_octonion_conj map_octonion_zero from
  MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Albert.Triality

/-- Coefficient maps between split coordinates, allowing different universes. -/
private def mapCoordinatesOfModel {R : Type v} {S : Type w} [CommRing R] [CommRing S]
    (f : R →+* S) (x : Model R) : Model S :=
  (fun i => f (x.1 i), fun i => mapCoordinates f (x.2 i))

private def modelAddHom {R : Type v} {S : Type w} [CommRing R] [CommRing S]
    (f : R →+* S) : Model R →+ Model S where
  toFun := mapCoordinatesOfModel f
  map_zero' := Prod.ext (funext fun _ => map_zero f) (funext fun _ => map_octonion_zero f)
  map_add' x y := Prod.ext (funext fun _ => map_add f _ _)
    (funext fun i => map_octonion_add f (x.2 i) (y.2 i))

private theorem mapCoordinatesOfModel_comp {R S T : Type*} [CommRing R] [CommRing S]
    [CommRing T] (f : R →+* S) (g : S →+* T) (x : Model R) :
    mapCoordinatesOfModel g (mapCoordinatesOfModel f x) =
      mapCoordinatesOfModel (g.comp f) x := rfl

private theorem mapCoordinatesOfModel_one {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) :
    mapCoordinatesOfModel f (CubicSpecification.cubicUnit : Model R) = (CubicSpecification.cubicUnit : Model S) :=
  Prod.ext (funext fun _ => map_one f) (funext fun _ => map_octonion_zero f)

private theorem mapCoordinatesOfModel_smul {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (r : R) (x : Model R) :
    mapCoordinatesOfModel f (r • x) = f r • mapCoordinatesOfModel f x :=
  Prod.ext (funext fun _ => map_mul f _ _) (funext fun i => map_octonion_smul f r (x.2 i))

private theorem mapCoordinatesOfModel_frameAxis {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (i : Fin 3) :
    mapCoordinatesOfModel f (FrameSpecification.frameAxis i : Model R) =
      (FrameSpecification.frameAxis i : Model S) := by
  apply Prod.ext
  · funext j
    change f ((Pi.single i 1 : Fin 3 → R) j) = (Pi.single i 1 : Fin 3 → S) j
    by_cases h : j = i <;> simp [h]
  · exact funext fun _ => map_octonion_zero f

private theorem mapCoordinatesOfModel_op {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (x y : Model R) :
    mapCoordinatesOfModel f (modelOp x y) =
      modelOp (mapCoordinatesOfModel f x) (mapCoordinatesOfModel f y) := by
  have hn (a : Zorn R) : f (norm R a) = norm S (mapCoordinates f a) :=
    (Zorn.mapCoordinates_norm f a).symm
  have hp (a b : Zorn R) :
      f ((norm R).polarBilin a b) =
        (norm S).polarBilin (mapCoordinates f a) (mapCoordinates f b) := by
    simp only [QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar, map_sub,
      hn, map_octonion_add]
  have ht (a b : Model R) :
      f (CubicSpecification.tracePairing (norm R) (fun _ => 1) a b) =
        CubicSpecification.tracePairing (norm S) (fun _ => 1)
          (mapCoordinatesOfModel f a) (mapCoordinatesOfModel f b) := by
    simp only [Albert.tracePairing_apply, CubicSpecification.blockWeight, Units.val_one, one_mul, map_sum,
      map_add, map_mul, hp, mapCoordinatesOfModel]
  have ha (a : Model R) :
      mapCoordinatesOfModel f (CubicSpecification.cubicAdjoint (norm R) (fun _ => 1) a) =
        CubicSpecification.cubicAdjoint (norm S) (fun _ => 1) (mapCoordinatesOfModel f a) := by
    apply Prod.ext
    · funext i
      simp only [mapCoordinatesOfModel, CubicSpecification.cubicAdjoint, CubicSpecification.blockWeight, Units.val_one, one_mul,
        map_sub, map_mul, hn]
    · funext i
      simp only [mapCoordinatesOfModel, CubicSpecification.cubicAdjoint, Units.val_one, one_smul,
        map_octonion_add, map_octonion_smul, map_octonion_conj, Zorn.mapCoordinates_mul, map_neg]
  have hAdd (a b : Model R) :
      mapCoordinatesOfModel f (a + b) =
        mapCoordinatesOfModel f a + mapCoordinatesOfModel f b := map_add (modelAddHom f) a b
  have hSub (a b : Model R) :
      mapCoordinatesOfModel f (a - b) =
        mapCoordinatesOfModel f a - mapCoordinatesOfModel f b := map_sub (modelAddHom f) a b
  simp only [modelOp, QuadraticOperatorSpecification.applyOperator, CubicSpecification.adjointCross,
    hSub, hAdd, mapCoordinatesOfModel_smul, ht, ha]

private def modelEquiv {R S : Type*} [CommRing R] [CommRing S] (e : R ≃+* S) :
    haveI := RingHomInvPair.of_ringEquiv e
    haveI := RingHomInvPair.of_ringEquiv_symm e
    Model R ≃ₛₗ[(↑e : R →+* S)] Model S :=
  haveI := RingHomInvPair.of_ringEquiv e
  haveI := RingHomInvPair.of_ringEquiv_symm e
  { toFun := mapCoordinatesOfModel e.toRingHom
    invFun := mapCoordinatesOfModel e.symm.toRingHom
    left_inv x := by
      rw [mapCoordinatesOfModel_comp, e.symm_toRingHom_comp_toRingHom]
      rfl
    right_inv x := by
      rw [mapCoordinatesOfModel_comp, e.toRingHom_comp_symm_toRingHom]
      rfl
    map_add' := map_add (modelAddHom e.toRingHom)
    map_smul' := mapCoordinatesOfModel_smul e.toRingHom }

private def transportModelAction {R S : Type*} [CommRing R] [CommRing S] (e : R ≃+* S) :
    (Model R ≃ₗ[R] Model R) ≃* (Model S ≃ₗ[S] Model S) :=
  haveI := RingHomInvPair.of_ringEquiv e
  haveI := RingHomInvPair.of_ringEquiv_symm e
  (LinearMap.GeneralLinearGroup.generalLinearEquiv R (Model R)).symm.trans
    ((LinearMap.GeneralLinearGroup.congrLinearEquiv (modelEquiv e)).trans
      (LinearMap.GeneralLinearGroup.generalLinearEquiv S (Model S)))

private theorem transportModelAction_apply {R S : Type*} [CommRing R] [CommRing S]
    (e : R ≃+* S) (a : Model R ≃ₗ[R] Model R) (x : Model R) :
    transportModelAction e a (mapCoordinatesOfModel e.toRingHom x) =
      mapCoordinatesOfModel e.toRingHom (a x) := by
  change modelEquiv e (a ((modelEquiv e).symm (modelEquiv e x))) = modelEquiv e (a x)
  rw [LinearEquiv.symm_apply_apply]

private theorem transportModelAction_isSplit {R S : Type*} [CommRing R] [CommRing S]
    (e : R ≃+* S) (a : Model R ≃ₗ[R] Model R) :
    IsSplitAutomorphism (transportModelAction e a) ↔ IsSplitAutomorphism a := by
  constructor
  · intro h
    have hinj := (modelEquiv e).injective
    refine ⟨hinj ?_, fun x y => hinj ?_⟩
    · change mapCoordinatesOfModel e.toRingHom (a CubicSpecification.cubicUnit) =
        mapCoordinatesOfModel e.toRingHom CubicSpecification.cubicUnit
      rw [← transportModelAction_apply, mapCoordinatesOfModel_one, h.1]
    · change mapCoordinatesOfModel e.toRingHom (a (modelOp x y)) =
        mapCoordinatesOfModel e.toRingHom (modelOp (a x) (a y))
      rw [← transportModelAction_apply, mapCoordinatesOfModel_op, h.2,
        transportModelAction_apply, transportModelAction_apply, mapCoordinatesOfModel_op]
  · intro h
    refine ⟨?_, fun x y => ?_⟩
    · rw [← mapCoordinatesOfModel_one e.toRingHom, transportModelAction_apply, h.1]
    · obtain ⟨x, rfl⟩ := (modelEquiv e).surjective x
      obtain ⟨y, rfl⟩ := (modelEquiv e).surjective y
      change transportModelAction e a (modelOp (mapCoordinatesOfModel e.toRingHom x)
        (mapCoordinatesOfModel e.toRingHom y)) =
          modelOp (transportModelAction e a (mapCoordinatesOfModel e.toRingHom x))
            (transportModelAction e a (mapCoordinatesOfModel e.toRingHom y))
      rw [← mapCoordinatesOfModel_op, transportModelAction_apply, h.2,
        mapCoordinatesOfModel_op, transportModelAction_apply, transportModelAction_apply]

open TrialitarianSplitTorus (modelCoordinateEquiv)
open private modelCoordinateEquiv_natural from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.TrialitarianSplitTorus

private theorem linearEquiv_ext_of_coordinates {R S : Type v} [CommRing R] [CommRing S]
    (f : R →+* S) (a b : Model S ≃ₗ[S] Model S)
    (h : ∀ x, a (mapModel f x) = b (mapModel f x)) : a = b := by
  classical
  apply LinearEquiv.toLinearMap_injective
  refine ((Pi.basisFun S (Fin 27)).map (modelCoordinateEquiv S).symm).ext fun i => ?_
  simp only [Module.Basis.map_apply, Pi.basisFun_apply]
  have he : mapModel f ((modelCoordinateEquiv R).symm (Pi.single i 1)) =
      (modelCoordinateEquiv S).symm (Pi.single i 1) := by
    apply (modelCoordinateEquiv S).injective
    rw [modelCoordinateEquiv_natural, LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]
    funext j
    by_cases hji : j = i <;> simp [hji]
  exact he ▸ h ((modelCoordinateEquiv R).symm (Pi.single i 1))

end ScalarCoordinates

section PointwiseSubgroup

open Matrix CategoryTheory.Limits
open _root_.Specs.LinearAlgebraicGroups.Albert.Automorphisms
  (MatrixSubgroup MatrixEquations MatrixCoordinates CutsOut)
open TrialitarianSplitTorus (modelCoordinateEquiv)
open private coordinateMatrixHom coordinateMatrixHom_mulVec matrixPointRepresentation
  modelCoordinateEquiv_natural from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.TrialitarianSplitTorus

variable {k : Type} [Field k]

private def vectorOver (v : Fin 3 → Fin 27 → k) (R : Type) [CommRing R] [Algebra k R]
    (i : Fin 3) : Fin 27 → R :=
  fun j => algebraMap k R (v i j)

private def vectorFixingMatrices (v : Fin 3 → Fin 27 → k) : MatrixSubgroup k (Fin 27) where
  subgroup R _ _ :=
    { carrier := {g | ∀ i, g.val *ᵥ vectorOver v R i = vectorOver v R i}
      one_mem' := fun i => Matrix.one_mulVec _
      mul_mem' := by
        intro g h hg hh i
        change (g.val * h.val) *ᵥ vectorOver v R i = _
        rw [← Matrix.mulVec_mulVec, hh i, hg i]
      inv_mem' := by
        intro g hg i
        change g⁻¹.val *ᵥ vectorOver v R i = _
        calc
          _ = g⁻¹.val *ᵥ (g.val *ᵥ vectorOver v R i) := by rw [hg i]
          _ = _ := by
            rw [Matrix.mulVec_mulVec, ← Matrix.GeneralLinearGroup.coe_mul, inv_mul_cancel]
            exact Matrix.one_mulVec _ }
  map_mem {R S} _ _ _ _ f g hg := by
    intro i
    funext j
    have hv : (f.toRingHom ∘ vectorOver v R i) = vectorOver v S i :=
      funext fun l => f.commutes (v i l)
    change ((g.val.map f.toRingHom *ᵥ vectorOver v S i) j) = _
    rw [← hv, ← RingHom.map_mulVec, hg i]
    rfl

private def vectorFixingEquations (v : Fin 3 → Fin 27 → k) :
    MatrixEquations k (Fin 27) where
  Index := Fin 3 × Fin 27
  finite := inferInstance
  equation R _ _ g i :=
    (g.val *ᵥ vectorOver v R i.1) i.2 - vectorOver v R i.1 i.2
  natural {R S} _ _ _ _ f g i := by
    rw [map_sub]
    congr 1
    · change f.toRingHom ((g.val *ᵥ vectorOver v _ i.1) i.2) = _
      have hv : (f.toRingHom ∘ vectorOver v R i.1) = vectorOver v S i.1 :=
        funext fun j => f.commutes (v i.1 j)
      rw [RingHom.map_mulVec, hv]
      rfl
    · exact f.commutes (v i.1 i.2)

private theorem vectorFixingEquations_iff (v : Fin 3 → Fin 27 → k)
    (R : Type) [CommRing R] [Algebra k R] (g : Matrix.GeneralLinearGroup (Fin 27) R) :
    g ∈ (vectorFixingMatrices v).subgroup R ↔
      ∀ i, (vectorFixingEquations v).equation R g i = 0 := by
  constructor
  · intro h i
    exact sub_eq_zero.mpr (congrFun (h i.1) i.2)
  · intro h i
    exact funext fun j => sub_eq_zero.mp (h (i, j))

private def intoFullMatrixPoints (k : Type) [Field k] :
    StandardGroups.generalLinearPoints k (Fin 27) ⟶
      (_root_.Specs.LinearAlgebraicGroups.Albert.Automorphisms.MatrixSubgroup.full k (Fin 27)).points where
  app _ := GrpCat.ofHom
    { toFun := fun g => ⟨g, Subgroup.mem_top _⟩
      map_one' := Subtype.ext rfl
      map_mul' _ _ := Subtype.ext rfl }
  naturality {_ _} _ := GrpCat.ext fun _ => Subtype.ext rfl

set_option backward.isDefEq.respectTransparency false in
/-- The pointwise fixer of the three vectors in the represented split group. -/
private theorem exists_vectorFixingSubgroup (L : AffineAlgebraicGroup k) (a : SplitAction L.val)
    (v : Fin 3 → Model k) :
    ∃ H : ClosedSubgroup L.val,
      ∀ (R : TestAlgebra k) (x : Points L.val.X R),
        (∃ h : Points H.group.X R, h ≫ H.inclusion.hom.hom = x) ↔
          ∀ i, a.action R x (mapModel (algebraMap k R) (v i)) =
            mapModel (algebraMap k R) (v i) := by
  let v' := fun i => modelCoordinateEquiv k (v i)
  let M := vectorFixingMatrices v'
  obtain ⟨c, hc, _⟩ := Albert.Automorphisms.matrixEquationsPresent k (Fin 27) M
    (vectorFixingEquations v') (vectorFixingEquations_iff v')
  obtain ⟨W, V, j, _, _, w, l, hj, _, hi⟩ :=
    Albert.Automorphisms.closedMatrixSubgroup k (Fin 27) M _ hc
  let n := matrixPointRepresentation a ≫ intoFullMatrixPoints k ≫ l.inv
  let f := (groupHomEquiv L.val V L.property.1).symm n
  have hf (R : TestAlgebra k) (x : Points L.val.X R) :
      (l.hom.app R (x ≫ f.hom.hom)).val = coordinateMatrixHom a R x := by
    have h := (groupHomEquiv L.val V L.property.1).apply_symm_apply n
    change (groupPointsFunctor k).map f = n at h
    have hh : (groupPointsFunctor k).map f ≫ l.hom =
        matrixPointRepresentation a ≫ intoFullMatrixPoints k := by simp [h, n]
    exact congrArg Subtype.val (DFunLike.congr_fun (congrArg (fun t => (t.app R).hom) hh) x)
  let square := IsPullback.of_hasPullback f j
  have hc := (Grp.forget (SchemeOver k) ⋙ Over.forget _).map_isPullback square
  let H : ClosedSubgroup L.val := ⟨pullback f j, pullback.fst f j,
    MorphismProperty.of_isPullback hc.flip hj⟩
  have hs := (Grp.forget (SchemeOver k)).map_isPullback square
  refine ⟨H, fun R x => ?_⟩
  have hlift :
      (∃ h : Points H.group.X R, h ≫ H.inclusion.hom.hom = x) ↔
        ∃ y : Points W.X R, y ≫ j.hom.hom = x ≫ f.hom.hom := by
    constructor
    · rintro ⟨h, rfl⟩
      have hw : (pullback.fst f j).hom.hom ≫ f.hom.hom =
          (pullback.snd f j).hom.hom ≫ j.hom.hom := hs.w
      refine ⟨h ≫ (pullback.snd f j).hom.hom, ?_⟩
      change (h ≫ (pullback.snd f j).hom.hom) ≫ j.hom.hom =
        h ≫ (pullback.fst f j).hom.hom ≫ f.hom.hom
      rw [Category.assoc, hw]
    · rintro ⟨y, hy⟩
      exact ⟨hs.lift x y hy.symm, hs.lift_fst _ _ _⟩
  rw [hlift]
  have he : (∃ y : Points W.X R, y ≫ j.hom.hom = x ≫ f.hom.hom) ↔
      coordinateMatrixHom a R x ∈ M.subgroup R := by
    constructor
    · rintro ⟨y, hy⟩
      have h := hi R y
      change (l.hom.app R (y ≫ j.hom.hom)).val = (w.hom.app R y).val at h
      rw [hy, hf] at h
      exact h ▸ (w.hom.app R y).property
    · intro h
      let m : M.subgroup R := ⟨coordinateMatrixHom a R x, h⟩
      let y := w.inv.app R m
      refine ⟨y, (l.app R).groupIsoToMulEquiv.injective (Subtype.ext ?_)⟩
      have hw : w.hom.app R y = m := (w.app R).groupIsoToMulEquiv.apply_symm_apply m
      have h := hi R y
      change (l.hom.app R (y ≫ j.hom.hom)).val = (w.hom.app R y).val at h
      exact h.trans ((congrArg Subtype.val hw).trans (hf R x).symm)
  rw [he]
  change (∀ i, (coordinateMatrixHom a R x).val *ᵥ vectorOver v' R i = vectorOver v' R i) ↔ _
  have hv (i : Fin 3) : vectorOver v' R i =
      modelCoordinateEquiv R (mapModel (algebraMap k R) (v i)) :=
    (modelCoordinateEquiv_natural _ _).symm
  simp only [hv, coordinateMatrixHom_mulVec, LinearEquiv.symm_apply_apply,
    (modelCoordinateEquiv R).injective.eq_iff]

end PointwiseSubgroup

section LiftTestAlgebras

variable {k : Type} [Field k]

private abbrev upCoefficients (A : Type) [CommRing A] : A ≃+* ULift.{u} A :=
  ULift.ringEquiv.symm

private abbrev liftAlgebraStructure (e : k ≃+* F) (R : TestAlgebra k) :
    Algebra F (ULift.{u} R) :=
  ((upCoefficients R).toRingHom.comp ((algebraMap k R).comp e.symm.toRingHom)).toAlgebra

private abbrev liftAlgebra (e : k ≃+* F) (R : TestAlgebra k) : TestAlgebra F :=
  @CommAlgCat.of F _ (ULift.{u} R) _ (liftAlgebraStructure e R)

private abbrev liftAlgebraScalars (e : k ≃+* F) (R : TestAlgebra k) :
    F →+* ULift.{u} R :=
  @algebraMap F (ULift.{u} R) _ _ (liftAlgebraStructure e R)

private def liftCoefficientsMap {R S : TestAlgebra k} (f : R ⟶ S) :
    ULift.{u} R →+* ULift.{u} S :=
  (upCoefficients S).toRingHom.comp (f.hom.toRingHom.comp ULift.ringEquiv.toRingHom)

private def liftAlgebraMap (e : k ≃+* F) {R S : TestAlgebra k} (f : R ⟶ S) :
    liftAlgebra e R ⟶ liftAlgebra e S := by
  letI := liftAlgebraStructure e R
  letI := liftAlgebraStructure e S
  exact CommAlgCat.ofHom
    { toRingHom := liftCoefficientsMap f
      commutes' x := by
        change ULift.up (f.hom (algebraMap k R (e.symm x))) =
          ULift.up (algebraMap k S (e.symm x))
        rw [f.hom.commutes] }

private def mapFromLift (e : k ≃+* F) (R : TestAlgebra k) (A : TestAlgebra F)
    (f : R →+* A) (hf : ∀ x, f (algebraMap k R x) = algebraMap F A (e x)) :
    liftAlgebra e R ⟶ A := by
  letI := liftAlgebraStructure e R
  exact CommAlgCat.ofHom
    { toRingHom := f.comp ULift.ringEquiv.toRingHom
      commutes' x := by
        change f (algebraMap k R (e.symm x)) = algebraMap F A x
        rw [hf, e.apply_symm_apply] }

private theorem mapPoints_comp {G : GroupScheme F} {R S A : TestAlgebra F}
    (f : R ⟶ S) (g : S ⟶ A) (p : Points G.X R) :
    mapPoints g (mapPoints f p) = mapPoints (f ≫ g) p := by
  change (testSpec F).map g.op ≫ (testSpec F).map f.op ≫ p =
    (testSpec F).map (g.op ≫ f.op) ≫ p
  rw [Functor.map_comp, Category.assoc]

end LiftTestAlgebras

section LaurentEvaluation

open LaurentPolynomial

private theorem laurentEval_comp {K R S : Type*} [CommRing K] [CommRing R] [CommRing S]
    (f : K →+* R) (g : R →+* S) (x : Rˣ) :
    g.comp (eval₂ f x) = eval₂ (g.comp f) (Units.map g.toMonoidHom x) := by
  apply IsLocalization.ringHom_ext (Submonoid.powers (Polynomial.X : Polynomial K))
  apply Polynomial.ringHom_ext
  · intro a
    change g (eval₂ f x (Polynomial.toLaurent (Polynomial.C a))) =
      eval₂ (g.comp f) (Units.map g.toMonoidHom x) (Polynomial.toLaurent (Polynomial.C a))
    simp only [Polynomial.toLaurent_C, eval₂_C, RingHom.comp_apply]
  · change g (eval₂ f x (Polynomial.toLaurent Polynomial.X)) =
      eval₂ (g.comp f) (Units.map g.toMonoidHom x) (Polynomial.toLaurent Polynomial.X)
    rw [Polynomial.toLaurent_X, eval₂_T, eval₂_T, zpow_one, zpow_one]
    rfl

private def laurentUnit (R : Type*) [CommRing R] : (LaurentPolynomial R)ˣ :=
  ⟨T 1, T (-1), by rw [← T_add]; exact T_zero, by rw [← T_add]; exact T_zero⟩

private theorem laurentEval_unit {K R : Type*} [CommRing K] [CommRing R]
    (f : K →+* R) (x : Rˣ) : Units.map (eval₂ f x).toMonoidHom (laurentUnit K) = x := by
  apply Units.ext
  change eval₂ f x (T 1) = _
  rw [eval₂_T, zpow_one]

variable {k : Type} [Field k]

private abbrev laurentTest (k : Type) [Field k] := CommAlgCat.of k (LaurentPolynomial k)

private def laurentEvaluation (k : Type) [Field k] (R : TestAlgebra k) (x : Rˣ) :
    laurentTest k ⟶ R :=
  CommAlgCat.ofHom ⟨eval₂ (algebraMap k R) x, eval₂_C _ _⟩

private def laurentEvaluationLift (e : k ≃+* F) (R : TestAlgebra F) (x : Rˣ) :
    liftAlgebra e (laurentTest k) ⟶ R :=
  mapFromLift e (laurentTest k) R (eval₂ ((algebraMap F R).comp e.toRingHom) x) (eval₂_C _ _)

private theorem laurentEvaluationLift_natural (e : k ≃+* F) {R S : TestAlgebra F}
    (f : R ⟶ S) (x : Rˣ) :
    laurentEvaluationLift e R x ≫ f =
      laurentEvaluationLift e S (Units.map f.hom.toMonoidHom x) := by
  letI := liftAlgebraStructure e (laurentTest k)
  apply CommAlgCat.hom_ext
  apply AlgHom.ext
  intro a
  have h := RingHom.congr_fun
    (laurentEval_comp ((algebraMap F R).comp e.toRingHom) f.hom.toRingHom x) a.down
  have hc : f.hom.toRingHom.comp ((algebraMap F R).comp e.toRingHom) =
      (algebraMap F S).comp e.toRingHom := RingHom.ext fun r => f.hom.commutes (e r)
  rw [hc] at h
  exact h

private theorem laurentEvaluationLift_small (e : k ≃+* F) (R : TestAlgebra k) (x : Rˣ) :
    laurentEvaluationLift e (liftAlgebra e R) (Units.map (upCoefficients R).toMonoidHom x) =
      liftAlgebraMap e (laurentEvaluation k R x) := by
  letI := liftAlgebraStructure e (laurentTest k)
  letI := liftAlgebraStructure e R
  apply CommAlgCat.hom_ext
  apply AlgHom.ext
  intro p
  have h := RingHom.congr_fun
    (laurentEval_comp (algebraMap k R) (upCoefficients R).toRingHom x) p.down
  have hc : (upCoefficients R).toRingHom.comp (algebraMap k R) =
      (liftAlgebraScalars e R).comp e.toRingHom := by
    apply RingHom.ext
    intro a
    change ULift.up (algebraMap k R a) = ULift.up (algebraMap k R (e.symm (e a)))
    rw [e.symm_apply_apply]
  rw [hc] at h
  exact h.symm

/-- Extending a natural family by evaluation of its universal Laurent point. -/
private theorem extendUnitFamily (e : k ≃+* F) (G : GroupScheme F)
    (a : ∀ R : TestAlgebra k, Rˣ →* Points G.X (liftAlgebra e R))
    (ha : ∀ {R S : TestAlgebra k} (f : R ⟶ S) (x : Rˣ),
      mapPoints (liftAlgebraMap e f) (a R x) = a S (Units.map f.hom.toMonoidHom x)) :
    ∃ b : ∀ R : TestAlgebra F, Rˣ →* Points G.X R,
      (∀ {R S : TestAlgebra F} (f : R ⟶ S) (x : Rˣ),
        mapPoints f (b R x) = b S (Units.map f.hom.toMonoidHom x)) ∧
      ∀ (R : TestAlgebra k) (x : Rˣ),
        b (liftAlgebra e R) (Units.map (upCoefficients R).toMonoidHom x) = a R x := by
  let p := a (laurentTest k) (laurentUnit k)
  let b (R : TestAlgebra F) (x : Rˣ) := mapPoints (laurentEvaluationLift e R x) p
  have hb {R S : TestAlgebra F} (f : R ⟶ S) (x : Rˣ) :
      mapPoints f (b R x) = b S (Units.map f.hom.toMonoidHom x) := by
    change mapPoints f (mapPoints (laurentEvaluationLift e R x) p) = _
    rw [mapPoints_comp, laurentEvaluationLift_natural]
  have hs (R : TestAlgebra k) (x : Rˣ) :
      b (liftAlgebra e R) (Units.map (upCoefficients R).toMonoidHom x) = a R x := by
    change mapPoints (laurentEvaluationLift e (liftAlgebra e R)
      (Units.map (upCoefficients R).toMonoidHom x)) p = _
    rw [laurentEvaluationLift_small, show p = a (laurentTest k) (laurentUnit k) from rfl, ha]
    exact congrArg (a R) (laurentEval_unit _ _)
  have hm (R : TestAlgebra F) (x y : Rˣ) : b R (x * y) = b R x * b R y := by
    let P := LaurentPolynomial k
    let Q := CommAlgCat.of k (LaurentPolynomial P)
    let x₀ : Qˣ := Units.map (algebraMap P Q).toMonoidHom (laurentUnit k)
    let y₀ : Qˣ := laurentUnit P
    let h₁ := eval₂ ((algebraMap F R).comp e.toRingHom) x
    let h₂ := eval₂ h₁ y
    let f := mapFromLift e Q R h₂ (fun r => by
      change eval₂ h₁ y (C (C r)) = algebraMap F R (e r)
      rw [eval₂_C]
      exact eval₂_C _ _ r)
    let m := (Units.map f.hom.toMonoidHom).comp (Units.map (upCoefficients Q).toMonoidHom)
    have hx : m x₀ = x := by
      apply Units.ext
      change eval₂ h₁ y (C (T 1)) = x.val
      rw [eval₂_C, eval₂_T, zpow_one]
    have hy : m y₀ = y := laurentEval_unit h₁ y
    have hq (z : Qˣ) : b R (m z) = mapPoints f (a Q z) := by
      change b R (Units.map f.hom.toMonoidHom (Units.map (upCoefficients Q).toMonoidHom z)) = _
      rw [← hb, hs]
    rw [← hx, ← hy, ← map_mul m, hq, hq, hq, map_mul]
    exact (MonObj.comp_mul _ _ _)
  let c (R : TestAlgebra F) : Rˣ →* Points G.X R :=
    { toFun := b R
      map_one' := mul_left_cancel (show b R 1 * b R 1 = b R 1 * 1 by
        rw [← hm, one_mul, mul_one])
      map_mul' := hm R }
  exact ⟨c, hb, hs⟩

end LaurentEvaluation

section GeometricComparison

open TrialitarianSplitTorus (extendSplitAction)
open TrialitarianSplitTorusSpecification (IsGeometricFrameConjugate integralPoint)
open IntegralSmoothnessSpecification (geometricFiber algebraicFiber SplitGroup)
open Albert.IntegralSmoothness (geometricFiberAction)
open ShortDirectionSpecification (IntegralPresentation)
open private geometricFiberPointEquiv geometricFiberPointEquiv_left from
  MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Albert.IntegralSmoothness
open private diagonal_sum from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.TrialitarianAlbertDescent
open private map_octonion_zero from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Albert.Triality

private def SpansDiagonal {R : Type*} [CommRing R] (v : Fin 3 → Model R) : Prop :=
  (∀ i, (v i).2 = 0) ∧ ∀ i, ∃ a : Fin 3 → R,
    FrameSpecification.frameAxis i = ∑ j, a j • v j

private theorem spansDiagonal_map {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S)
    {v : Fin 3 → Model R} (hv : SpansDiagonal v) :
    SpansDiagonal (fun i => mapCoordinatesOfModel f (v i)) := by
  refine ⟨fun i => ?_, fun i => ?_⟩
  · funext j
    change Composition.ZornSpecification.mapCoordinates f ((v i).2 j) = 0
    rw [hv.1 i]
    exact map_octonion_zero f
  · obtain ⟨a, ha⟩ := hv.2 i
    refine ⟨fun j => f (a j), ?_⟩
    have h := congrArg (modelAddHom f) ha
    rw [map_sum] at h
    change mapCoordinatesOfModel f (FrameSpecification.frameAxis i) =
      ∑ j, mapCoordinatesOfModel f (a j • v j) at h
    simpa only [mapCoordinatesOfModel_frameAxis, mapCoordinatesOfModel_smul] using h

private theorem fixesDiagonal_iff {k : Type u} [Field k] (R : TestAlgebra k)
    (g : Model R ≃ₗ[R] Model R)
    {v : Fin 3 → Model R} (hv : SpansDiagonal v) :
    (∀ i, g (v i) = v i) ↔ ∀ i, g (FrameSpecification.frameAxis i) = FrameSpecification.frameAxis i := by
  constructor
  · intro h i
    obtain ⟨a, ha⟩ := hv.2 i
    rw [ha]
    simp only [map_sum, map_smul, h]
  · intro h i
    have hdiag : v i = ((v i).1, 0) := Prod.ext rfl (hv.1 i)
    rw [hdiag, diagonal_sum R]
    simp only [map_sum, map_smul, h]

private theorem conjugate_fixes_iff {R : Type*} [CommRing R] (a b : Model R ≃ₗ[R] Model R)
    (x : Model R) : (a * b * a⁻¹) (a x) = a x ↔ b x = x := by
  change a (b (a.symm (a x))) = a x ↔ b x = x
  rw [LinearEquiv.symm_apply_apply, a.injective.eq_iff]

set_option backward.isDefEq.respectTransparency false in
private theorem liftsAfterBaseChange {k K : Type} [Field k] [Field K] [Algebra k K]
    {H G : GroupScheme k} (i : H ⟶ G) (R : TestAlgebra K)
    (x : Points ((groupBaseChange k K).obj G).X R) :
    (∃ h : Points ((groupBaseChange k K).obj H).X R,
      h ≫ ((groupBaseChange k K).map i).hom.hom = x) ↔
      ∃ h : Points H.X ((restrictTestAlgebra k K).obj R),
        h ≫ i.hom.hom = baseChangePoint k K G.X R x := by
  let E := baseChangePointGroupEquiv K H R
  let D := baseChangePointGroupEquiv K G R
  have hcomp (h : Points ((groupBaseChange k K).obj H).X R) :
      D (h ≫ ((groupBaseChange k K).map i).hom.hom) = E h ≫ i.hom.hom :=
    baseChangePointsSchemeNaturality k K i.hom.hom R h
  change _ ↔ ∃ h, h ≫ i.hom.hom = D x
  constructor
  · rintro ⟨h, rfl⟩
    exact ⟨E h, (hcomp h).symm⟩
  · rintro ⟨h, hh⟩
    exact ⟨E.symm h, D.injective ((hcomp _).trans
      ((congrArg (· ≫ i.hom.hom) (E.apply_symm_apply h)).trans hh))⟩

set_option backward.isDefEq.respectTransparency false in
/-- A split automorphism carrying the three vectors onto generators of the
diagonal yields conjugacy of the entire subgroup functors. -/
private theorem geometricConjugacyOfSpanning {k : Type} [Field k]
    {P : IntegralPresentation} (L : SplitGroup P) (H : ClosedSubgroup (geometricFiber L k))
    (v : Fin 3 → Model k)
    (hv : ∀ (R : TestAlgebra k) (x : Points (geometricFiber L k).X R),
      (∃ h : Points H.group.X R, h ≫ H.inclusion.hom.hom = x) ↔
        ∀ i, (geometricFiberAction L k).action R x (mapModel (algebraMap k R) (v i)) =
          mapModel (algebraMap k R) (v i))
    (j : Model (AlgebraicClosure k) ≃ₗ[AlgebraicClosure k] Model (AlgebraicClosure k))
    (hj : IsSplitAutomorphism j)
    (hd : SpansDiagonal (fun i => j (mapModel (algebraMap k (AlgebraicClosure k)) (v i)))) :
    IsGeometricFrameConjugate H := by
  let K := AlgebraicClosure k
  let C := CommAlgCat.of K K
  let L₀ := geometricFiber L k
  let A := geometricFiberAction L k
  let A' := extendSplitAction (K := K) A
  obtain ⟨p, hp⟩ : j ∈ Set.range (A'.action C) := by
    rw [A'.image]
    exact hj
  refine ⟨p, fun R x => ?_⟩
  let f : C ⟶ R := CommAlgCat.ofHom (Algebra.ofId K R)
  let R' := (restrictTestAlgebra k K).obj R
  let a := A'.action R (mapPoints f p)
  let b := A'.action R x
  let w (i : Fin 3) : Model R := mapModel (algebraMap k R') (v i)
  have hw (i : Fin 3) : w i = mapModel f.hom.toRingHom
      (mapModel (algebraMap k K) (v i)) := rfl
  have ha (i : Fin 3) : a (w i) =
      mapModel f.hom.toRingHom (j (mapModel (algebraMap k K) (v i))) := by
    rw [hw]
    have h := A'.natural f p (mapModel (algebraMap k K) (v i))
    rw [hp] at h
    exact h.symm
  have hs : SpansDiagonal (fun i => a (w i)) := by
    simp only [ha]
    exact spansDiagonal_map f.hom.toRingHom hd
  have hl := (liftsAfterBaseChange H.inclusion R x).trans
    (hv R' (baseChangePoint k K L₀.X R x))
  change _ ↔ ∀ i, L.action _ (integralPoint
    (baseChangePoint k K L₀.X R (mapPoints f p * x * (mapPoints f p)⁻¹))) _ = _
  rw [hl]
  let z := baseChangePoint k K L₀.X R (mapPoints f p * x * (mapPoints f p)⁻¹)
  have hz : integralPoint (G := L) z = geometricFiberPointEquiv L R' z := by
    apply Over.OverMorphism.ext
    exact (geometricFiberPointEquiv_left L R' z).symm
  change (∀ i, b (w i) = w i) ↔
    ∀ i, L.action _ (integralPoint (G := L) z) (FrameSpecification.frameAxis i) =
      FrameSpecification.frameAxis i
  rw [hz]
  change (∀ i, b (w i) = w i) ↔
    ∀ i, A'.action R (mapPoints f p * x * (mapPoints f p)⁻¹)
      (FrameSpecification.frameAxis i) = FrameSpecification.frameAxis i
  simp only [map_mul, map_inv]
  change (∀ i, b (w i) = w i) ↔
    ∀ i, (a * b * a⁻¹) (FrameSpecification.frameAxis i) = FrameSpecification.frameAxis i
  rw [← fixesDiagonal_iff R (a * b * a⁻¹) hs]
  exact forall_congr' (fun i => (conjugate_fixes_iff a b (w i)).symm)

end GeometricComparison

section TransferStabilizer

private def FixesVectors {k : Type v} [Field k] {L : GroupScheme k}
    (H : ClosedSubgroup L) (a : SplitAction L) (v : Fin 3 → Model k) : Prop :=
  ∀ (R : TestAlgebra k) (x : Points L.X R),
    (∃ h : Points H.group.X R, h ≫ H.inclusion.hom.hom = x) ↔
      ∀ i, a.action R x (mapModel (algebraMap k R) (v i)) = mapModel (algebraMap k R) (v i)

private def fixingAction {k : Type v} [Field k] {L : GroupScheme k}
    (H : ClosedSubgroup L) (a : SplitAction L) (R : TestAlgebra k) :
    Points H.group.X R →* (Model R ≃ₗ[R] Model R) :=
  (a.action R).comp (((groupPointsFunctor k).map H.inclusion).app R).hom

private theorem fixingAction_injective {k : Type v} [Field k] {L : GroupScheme k}
    (H : ClosedSubgroup L) (a : SplitAction L) (R : TestAlgebra k) :
    Function.Injective (fixingAction H a R) := by
  intro x y h
  haveI : IsClosedImmersion H.inclusion.hom.hom.left := H.isClosedImmersion
  letI : Mono H.inclusion.hom.hom := Over.mono_of_mono_left _
  apply (cancel_mono H.inclusion.hom.hom).mp
  exact a.injective R h

private theorem fixingAction_natural {k : Type v} [Field k] {L : GroupScheme k}
    (H : ClosedSubgroup L) (a : SplitAction L) {R S : TestAlgebra k}
    (f : R ⟶ S) (x : Points H.group.X R) (y : Model R) :
    mapModel f.hom.toRingHom (fixingAction H a R x y) =
      fixingAction H a S (mapPoints f x) (mapModel f.hom.toRingHom y) := by
  change mapModel f.hom.toRingHom (a.action R (x ≫ H.inclusion.hom.hom) y) =
    a.action S (((testSpec k).map f.op ≫ x) ≫ H.inclusion.hom.hom) (mapModel f.hom.toRingHom y)
  rw [Category.assoc]
  exact a.natural f _ _

private theorem fixingAction_image {k : Type v} [Field k] {L : GroupScheme k}
    (H : ClosedSubgroup L) (a : SplitAction L) (v : Fin 3 → Model k)
    (hv : FixesVectors H a v) (R : TestAlgebra k) :
    Set.range (fixingAction H a R) =
      {x | IsSplitAutomorphism x ∧
        ∀ i, x (mapModel (algebraMap k R) (v i)) = mapModel (algebraMap k R) (v i)} := by
  ext g
  constructor
  · rintro ⟨x, rfl⟩
    refine ⟨?_, (hv R (x ≫ H.inclusion.hom.hom)).mp ⟨x, rfl⟩⟩
    change a.action R (x ≫ H.inclusion.hom.hom) ∈ {y | IsSplitAutomorphism y}
    rw [← a.image]
    exact ⟨_, rfl⟩
  · rintro ⟨hg, hfix⟩
    have h : g ∈ Set.range (a.action R) := (a.image R).symm ▸ hg
    obtain ⟨x, rfl⟩ := h
    obtain ⟨y, hy⟩ := (hv R x).mpr hfix
    exact ⟨y, congrArg (a.action R) hy⟩

variable {k : Type} [Field k]

private theorem mapLiftedVector (e : k ≃+* F) (R : TestAlgebra k) (v : Model k) :
    mapCoordinatesOfModel (upCoefficients R).toRingHom (mapModel (algebraMap k R) v) =
      mapModel (liftAlgebraScalars e R) (mapCoordinatesOfModel e.toRingHom v) := by
  change mapCoordinatesOfModel (upCoefficients R).toRingHom
      (mapCoordinatesOfModel (algebraMap k R) v) =
    mapCoordinatesOfModel (liftAlgebraScalars e R)
      (mapCoordinatesOfModel e.toRingHom v)
  rw [mapCoordinatesOfModel_comp, mapCoordinatesOfModel_comp]
  congr 1
  apply RingHom.ext
  intro r
  change ULift.up (algebraMap k R r) = ULift.up (algebraMap k R (e.symm (e r)))
  rw [e.symm_apply_apply]

private theorem mapLiftedModel_natural {R S : TestAlgebra k} (f : R ⟶ S)
    (x : Model R) :
    mapModel (liftCoefficientsMap.{u} f) (mapCoordinatesOfModel (upCoefficients R).toRingHom x) =
      mapCoordinatesOfModel (upCoefficients S).toRingHom (mapModel f.hom.toRingHom x) := by
  change mapCoordinatesOfModel (liftCoefficientsMap.{u} f)
      (mapCoordinatesOfModel (upCoefficients R).toRingHom x) =
    mapCoordinatesOfModel (upCoefficients S).toRingHom (mapCoordinatesOfModel f.hom.toRingHom x)
  rw [mapCoordinatesOfModel_comp, mapCoordinatesOfModel_comp]
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- The same vector-fixing condition gives an injective natural map from the
small stabilizer points to the actual points on lifted test algebras. -/
private theorem liftFixingPoints (e : k ≃+* F) {L : GroupScheme k} {J : GroupScheme F}
    (H : ClosedSubgroup L) (B : ClosedSubgroup J) (a : SplitAction L) (b : SplitAction J)
    (v : Fin 3 → Model k) (hH : FixesVectors H a v)
    (hB : FixesVectors B b (fun i => mapCoordinatesOfModel e.toRingHom (v i))) :
    ∃ p : ∀ R : TestAlgebra k, Points H.group.X R →* Points B.group.X (liftAlgebra e R),
      (∀ R, Function.Injective (p R)) ∧
      ∀ {R S : TestAlgebra k} (f : R ⟶ S) (x : Points H.group.X R),
        mapPoints (liftAlgebraMap e f) (p R x) = p S (mapPoints f x) := by
  let T (R : TestAlgebra k) := transportModelAction (upCoefficients R)
  have hex (R : TestAlgebra k) (x : Points H.group.X R) :
      ∃ y : Points B.group.X (liftAlgebra e R),
        fixingAction B b (liftAlgebra e R) y = T R (fixingAction H a R x) := by
    change T R (fixingAction H a R x) ∈ Set.range (fixingAction B b (liftAlgebra e R))
    rw [fixingAction_image B b _ hB]
    have hx : fixingAction H a R x ∈ Set.range (fixingAction H a R) := ⟨x, rfl⟩
    rw [fixingAction_image H a v hH] at hx
    refine ⟨(transportModelAction_isSplit _ _).mpr hx.1, fun i => ?_⟩
    rw [← mapLiftedVector e R (v i)]
    exact (transportModelAction_apply _ _ _).trans
      (congrArg (mapCoordinatesOfModel (upCoefficients R).toRingHom) (hx.2 i))
  choose p hp using hex
  let q (R : TestAlgebra k) : Points H.group.X R →* Points B.group.X (liftAlgebra e R) :=
    { toFun := p R
      map_one' := by
        apply fixingAction_injective B b
        change fixingAction B b _ (p R 1) = fixingAction B b _ 1
        rw [hp, map_one, map_one, map_one]
      map_mul' x y := by
        apply fixingAction_injective B b
        rw [hp, map_mul (fixingAction H a R), map_mul (T R),
          map_mul (fixingAction B b (liftAlgebra e R)), hp, hp] }
  refine ⟨q, ?_, ?_⟩
  · intro R x y h
    apply fixingAction_injective H a R
    apply (T R).injective
    exact (hp R x).symm.trans ((congrArg (fixingAction B b _) h).trans (hp R y))
  · intro R S f x
    apply fixingAction_injective B b
    apply linearEquiv_ext_of_coordinates (liftCoefficientsMap.{u} f)
    intro y
    obtain ⟨z, hz⟩ := (modelEquiv (upCoefficients R)).surjective y
    change mapCoordinatesOfModel (upCoefficients R).toRingHom z = y at hz
    subst y
    refine (fixingAction_natural B b (liftAlgebraMap e f) (p R x)
      (mapCoordinatesOfModel (upCoefficients R).toRingHom z)).symm.trans ?_
    change mapModel (liftCoefficientsMap.{u} f)
        (fixingAction B b _ (p R x) (mapCoordinatesOfModel (upCoefficients R).toRingHom z)) =
      fixingAction B b _ (p S (mapPoints f x))
        (mapModel (liftCoefficientsMap.{u} f)
          (mapCoordinatesOfModel (upCoefficients R).toRingHom z))
    rw [hp, hp]
    simp only [T, mapLiftedModel_natural, transportModelAction_apply, fixingAction_natural]

end TransferStabilizer

section MarkedAlbertModel

open private fixes_cubicInclusion_iff from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.TrialitarianAlbertDescent
open private map_octonion_zero from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Albert.Triality

private def splitActionOfChart (J : AlbertModel F)
    (c : ∀ R : TestAlgebra F, SplitChart J.law R)
    (hc : ∀ {R T : TestAlgebra F} (f : R ⟶ T) (x : R ⊗[F] J.V),
      mapModel f.hom.toRingHom ((c R).coordinates x) =
        (c T).coordinates (TensorProduct.map f.hom.toLinearMap LinearMap.id x)) :
    SplitAction J.automorphisms.val where
  action R := actionInCoordinates J R (c R)
  injective R := actionInCoordinates_injective J R (c R)
  image R := actionInCoordinates_image J R (c R)
  natural := actionInCoordinates_natural J c hc

private theorem groundCoordinates_natural (J : AlbertModel F)
    (c : ∀ R : TestAlgebra F, SplitChart J.law R)
    (hc : ∀ {R T : TestAlgebra F} (f : R ⟶ T) (x : R ⊗[F] J.V),
      mapModel f.hom.toRingHom ((c R).coordinates x) =
        (c T).coordinates (TensorProduct.map f.hom.toLinearMap LinearMap.id x))
    (R : TestAlgebra F) (x : J.V) :
    mapModel (algebraMap F R) ((c (CommAlgCat.of F F)).coordinates (1 ⊗ₜ[F] x)) =
      (c R).coordinates (1 ⊗ₜ[F] x) := by
  let f := CommAlgCat.ofHom (Algebra.ofId F R)
  have h := hc f (1 ⊗ₜ[F] x)
  rw [TensorProduct.map_tmul, LinearMap.id_apply, AlgHom.toLinearMap_apply, map_one] at h
  exact h

private theorem cubicFixesVectors {E : Type u} [Field E] [Algebra F E]
    {J : AlbertModel F} (B : CubicStabilizer J E) (d : Module.Basis (Fin 3) F E)
    (c : ∀ R : TestAlgebra F, SplitChart J.law R)
    (hc : ∀ {R T : TestAlgebra F} (f : R ⟶ T) (x : R ⊗[F] J.V),
      mapModel f.hom.toRingHom ((c R).coordinates x) =
        (c T).coordinates (TensorProduct.map f.hom.toLinearMap LinearMap.id x)) :
    FixesVectors B.stabilizer (splitActionOfChart J c hc)
      (fun i => (c (CommAlgCat.of F F)).coordinates (1 ⊗ₜ[F] B.diagonal (d i))) := by
  intro R g
  rw [← B.fixesExactly]
  have h := fixes_cubicInclusion_iff
    (d.reindex (Equiv.ulift.symm : Fin 3 ≃ ULift.{u} (Fin 3))) B.diagonal R (J.action R g)
  simp only [Module.Basis.reindex_apply, Equiv.symm_symm, Equiv.ulift_apply, ULift.forall] at h
  rw [h]
  change _ ↔ ∀ i, actionInCoordinates J R (c R) g
    (mapModel (algebraMap F R) ((c (CommAlgCat.of F F)).coordinates (1 ⊗ₜ[F] B.diagonal (d i)))) =
      mapModel (algebraMap F R) ((c (CommAlgCat.of F F)).coordinates (1 ⊗ₜ[F] B.diagonal (d i)))
  simp only [groundCoordinates_natural J c hc, actionInCoordinates_apply,
    (c R).coordinates.injective.eq_iff]

private theorem spanningOfDiagonalRange {E K : Type u} [Field E] [Field K]
    [Algebra F E] [Algebra F K] {J : AlbertModel F} (B : CubicStabilizer J E)
    (d : Module.Basis (Fin 3) F E) (t : K ⊗[F] J.V ≃ₗ[K] Model K)
    (ht : Set.range (fun x => t (B.diagonal.baseChange K x)) = {v | v.2 = 0}) :
    SpansDiagonal (fun i => t (1 ⊗ₜ[F] B.diagonal (d i))) := by
  let p := t.toLinearMap.comp (B.diagonal.baseChange K)
  let e := d.baseChange K
  have he (i : Fin 3) : p (e i) = t (1 ⊗ₜ[F] B.diagonal (d i)) := by
    simp [p, e, Module.Basis.baseChange_apply, LinearMap.baseChange_tmul]
  refine ⟨fun i => ?_, fun i => ?_⟩
  · have h : p (e i) ∈ Set.range p := ⟨_, rfl⟩
    change p (e i) ∈ Set.range (fun x => t (B.diagonal.baseChange K x)) at h
    rw [ht, he] at h
    exact h
  · have h : (FrameSpecification.frameAxis i : Model K) ∈ Set.range p := by
      change (FrameSpecification.frameAxis i : Model K) ∈
        Set.range (fun x => t (B.diagonal.baseChange K x))
      rw [ht]
      rfl
    obtain ⟨x, hx⟩ := h
    refine ⟨fun j => e.repr x j, hx.symm.trans ?_⟩
    calc
      p x = p (∑ j, e.repr x j • e j) := congrArg p (e.sum_repr x).symm
      _ = _ := by simp only [map_sum, map_smul, he]

set_option backward.isDefEq.respectTransparency false in
private theorem exists_markedChart {E S : Type u} [Field E] [Field S]
    [Algebra F E] [Algebra F S] [Algebra E S] [IsScalarTower F E S]
    [Module.Finite F E] [IsSepClosure F S] {G : AffineAlgebraicGroup F}
    {D : DiagramPresentation G E S} (M : CubicVectorModel G D)
    (degree : Module.finrank F E = 3) (d : Module.Basis (Fin 3) F E) :
    ∃ t : SplitChart M.albert.law (AlgebraicClosure F),
      SpansDiagonal (fun i => t.coordinates (1 ⊗ₜ[F] M.cubic.diagonal (d i))) := by
  let K := AlgebraicClosure F
  let f : S →ₐ[F] K := IsAlgClosed.lift
  letI : Algebra S K := f.toRingHom.toAlgebra
  letI : IsScalarTower F S K := IsScalarTower.of_algebraMap_eq' f.comp_algebraMap.symm
  let t₀ : SplitChart M.albert.law S := ⟨M.coordinates, M.unit, M.law⟩
  let t := extendChart t₀ f
  have hd (x : E) : t.coordinates (1 ⊗ₜ[F] M.cubic.diagonal x) =
      (fun i => algebraMap S K (D.numbering.symm i x), 0) := by
    have h := extendChart_apply t₀ f (1 ⊗ₜ[F] M.cubic.diagonal x)
    rw [LinearMap.rTensor_tmul, AlgHom.toLinearMap_apply, map_one,
      show t₀.coordinates (1 ⊗ₜ[F] M.cubic.diagonal x) =
        (fun i => D.numbering.symm i x, 0) from M.diagonal x] at h
    exact h.trans (Prod.ext rfl (funext fun _ => map_octonion_zero f.toRingHom))
  have h := TrialitarianAlbertDescent.splitChart_cubicDiagonalRange M.cubic
    (CommAlgCat.of F K) degree D.numbering t.coordinates hd
  exact ⟨t, spanningOfDiagonalRange M.cubic d t.coordinates h⟩

private theorem smallTransition {k : Type} [Field k] (e : k ≃+* F)
    (v : Fin 3 → Model k) (j : Model (AlgebraicClosure F) ≃ₗ[AlgebraicClosure F]
      Model (AlgebraicClosure F)) (hj : IsSplitAutomorphism j)
    (hspan : SpansDiagonal (fun i => j (mapModel (algebraMap F (AlgebraicClosure F))
      (mapCoordinatesOfModel e.toRingHom (v i))))) :
    ∃ p : Model (AlgebraicClosure k) ≃ₗ[AlgebraicClosure k] Model (AlgebraicClosure k),
      IsSplitAutomorphism p ∧
        SpansDiagonal (fun i => p (mapModel (algebraMap k (AlgebraicClosure k)) (v i))) := by
  let K := AlgebraicClosure k
  let L := AlgebraicClosure F
  let e' := IsAlgClosure.equivOfEquiv K L e
  let m := transportModelAction e'
  let p := m.symm j
  have hp : m p = j := m.apply_symm_apply j
  refine ⟨p, (transportModelAction_isSplit e' p).mp (hp.symm ▸ hj), ?_⟩
  have he (i : Fin 3) :
      mapCoordinatesOfModel e'.toRingHom (mapModel (algebraMap k K) (v i)) =
        mapModel (algebraMap F L) (mapCoordinatesOfModel e.toRingHom (v i)) := by
    change mapCoordinatesOfModel e'.toRingHom
      (mapCoordinatesOfModel (algebraMap k K) (v i)) =
        mapCoordinatesOfModel (algebraMap F L) (mapCoordinatesOfModel e.toRingHom (v i))
    rw [mapCoordinatesOfModel_comp, mapCoordinatesOfModel_comp]
    exact congrArg (fun f : k →+* L => mapCoordinatesOfModel f (v i))
      (IsAlgClosure.equivOfEquiv_comp_algebraMap K L e)
  have ht (i : Fin 3) :
      mapCoordinatesOfModel e'.toRingHom (p (mapModel (algebraMap k K) (v i))) =
        j (mapModel (algebraMap F L) (mapCoordinatesOfModel e.toRingHom (v i))) := by
    rw [← transportModelAction_apply, he]
    exact congrArg (fun q : Model L ≃ₗ[L] Model L => q _) hp
  have hs := spansDiagonal_map e'.symm.toRingHom hspan
  have hv : (fun i => mapCoordinatesOfModel e'.symm.toRingHom
        (j (mapModel (algebraMap F L) (mapCoordinatesOfModel e.toRingHom (v i))))) =
      fun i => p (mapModel (algebraMap k K) (v i)) := by
    funext i
    rw [← ht, mapCoordinatesOfModel_comp, e'.symm_toRingHom_comp_toRingHom]
    rfl
  exact hv ▸ hs

end MarkedAlbertModel

section Cocharacters

open CategoryTheory.CartesianMonoidalCategory
open IntegralSmoothnessSpecification (algebraicFiber)
open Albert.IntegralSmoothness (geometricFiberAction)
open private multiplicative_group_iso from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Relative.LeviConjugacy

private def constantUnitPoints (k Index : Type v) [Field k] :
    StandardGroups.multiplicativePoints k ⟶ StandardGroups.multiplicativePowerPoints k Index where
  app R := GrpCat.ofHom (MonoidHom.pi fun _ => MonoidHom.id Rˣ)
  naturality {_ _} _ := GrpCat.ext fun _ => rfl

private def evalUnitPoint (k Index : Type v) [Field k] (i : Index) :
    StandardGroups.multiplicativePowerPoints k Index ⟶ StandardGroups.multiplicativePoints k where
  app _ := GrpCat.ofHom (Pi.evalMonoidHom _ i)
  naturality {_ _} _ := GrpCat.ext fun _ => rfl

private theorem unitsFromPositiveTorus {k : Type} [Field k] {G : GroupScheme k}
    (T : ClosedSubgroup G) {r : ℕ} (hr : 0 < r)
    (e : T.group ≅ (StandardGroups.multiplicativePowerGroup k (ULift (Fin r))).val) :
    ∃ n : StandardGroups.multiplicativePoints k ⟶ (groupPointsFunctor k).obj G,
      ∀ R, Function.Injective (n.app R) := by
  let I := ULift (Fin r)
  let E := StandardGroups.multiplicativePowerGroupPointsIso k I
  let a := (groupPointsFunctor k).map e.inv
  let b := (groupPointsFunctor k).map T.inclusion
  refine ⟨constantUnitPoints k I ≫ E.inv ≫ a ≫ b, fun R x y h => ?_⟩
  haveI : IsClosedImmersion T.inclusion.hom.hom.left := T.isClosedImmersion
  letI : Mono T.inclusion.hom.hom := Over.mono_of_mono_left _
  letI : IsIso e.inv.hom.hom := (Grp.forget (SchemeOver k)).map_isIso e.inv
  change (E.inv.app R (fun _ : I => x) ≫ e.inv.hom.hom) ≫ T.inclusion.hom.hom =
    (E.inv.app R (fun _ : I => y) ≫ e.inv.hom.hom) ≫ T.inclusion.hom.hom at h
  have h' := (cancel_mono e.inv.hom.hom).mp ((cancel_mono T.inclusion.hom.hom).mp h)
  have he := (E.app R).symm.groupIsoToMulEquiv.injective h'
  exact congrFun he (⟨⟨0, hr⟩⟩ : I)

private theorem nonzeroCocharacterOfUnits (G : GroupScheme F)
    (a : ∀ R : TestAlgebra F, Rˣ →* Points G.X R)
    (ha : ∀ {R S : TestAlgebra F} (f : R ⟶ S) (x : Rˣ),
      mapPoints f (a R x) = a S (Units.map f.hom.toMonoidHom x))
    (hne : ∃ (R : TestAlgebra F) (x : Rˣ), a R x ≠ 1) :
    ∃ c : CharacterDescent.Cocharacter G, c ≠ 0 := by
  let I := ULift.{u} (Fin 1)
  let A := StandardGroups.multiplicativePowerGroup F I
  let E := StandardGroups.multiplicativePowerGroupPointsIso F I
  let n : StandardGroups.multiplicativePoints F ⟶ (groupPointsFunctor F).obj G :=
    { app := fun R => GrpCat.ofHom (a R)
      naturality := fun {_ _} f => GrpCat.ext fun x => (ha f x).symm }
  let p := E.hom ≫ evalUnitPoint F I ⟨0⟩ ≫ n
  let q := groupHomEquiv A.val G A.property.1
  let c := q.symm p
  have hc : c ≠ 0 := by
    intro hz
    obtain ⟨R, t, ht⟩ := hne
    let x := E.inv.app R (fun _ : I => t)
    have h := DFunLike.congr_fun (congrArg (fun τ => (τ.app R).hom) (q.apply_symm_apply p)) x
    have he : E.hom.app R x = (fun _ : I => t) :=
      (E.app R).groupIsoToMulEquiv.apply_symm_apply _
    change x ≫ c.hom.hom = a R ((E.hom.app R x : I → Rˣ) ⟨0⟩) at h
    rw [he, hz] at h
    exact ht (h.symm.trans (MonObj.comp_one x))
  obtain ⟨i⟩ : Nonempty (_ ≅ A.val) := multiplicative_group_iso (k := F)
  refine ⟨i.hom ≫ c, fun h => hc ((cancel_epi i.hom).mp ?_)⟩
  exact h.trans (comp_zero (f := i.hom) (Z := G)).symm

end Cocharacters

section Isotropy

open IntegralSmoothnessSpecification (algebraicFiber)
open Albert.IntegralSmoothness (geometricFiberAction)

set_option maxHeartbeats 900000 in
set_option backward.isDefEq.respectTransparency false in
private theorem albertIsotropyFromModel (F E S : Type u) [Field F] [ValuativeRel F]
    [TopologicalSpace F] [IsNonarchimedeanLocalField F] [Field E] [Field S]
    [Algebra F E] [Algebra F S] [Algebra E S] [IsScalarTower F E S]
    [Module.Finite F E] [IsSepClosure F S]
    (degree : Module.finrank F E = 3) (G : AffineAlgebraicGroup F)
    (D : DiagramPresentation G E S) (hG : GeometricRadicals.IsSemisimple G)
    (M : CubicVectorModel G D) :
    ∃ c : CharacterDescent.Cocharacter G.val, ¬ RelativeRank.IsCentralCocharacter c := by
  let J := M.albert
  let B := M.cubic
  haveI := localFieldSmall F
  let k := Shrink.{0} F
  let e : k ≃+* F := Shrink.ringEquiv F
  letI : TopologicalSpace k := TopologicalSpace.induced e ‹TopologicalSpace F›
  letI : ValuativeRel k := ValuativeRel.ofValuation ((ValuativeRel.valuation F).comap e.toRingHom)
  haveI : IsNonarchimedeanLocalField k := localFieldTransport e
  obtain ⟨c, hc⟩ := splitCharts J
    (SplitAlbertLocalForms.localAlbertSplitting.{u,u} F J.law J.albert)
  let d : Module.Basis (Fin 3) F E := (Module.finBasis F E).reindex (finCongr degree)
  let vF (i : Fin 3) := (c (CommAlgCat.of F F)).coordinates (1 ⊗ₜ[F] B.diagonal (d i))
  let v (i : Fin 3) := mapCoordinatesOfModel e.symm.toRingHom (vF i)
  have hv (i : Fin 3) : mapCoordinatesOfModel e.toRingHom (v i) = vF i := by
    change mapCoordinatesOfModel e.toRingHom (mapCoordinatesOfModel e.symm.toRingHom (vF i)) = _
    rw [mapCoordinatesOfModel_comp, e.toRingHom_comp_symm_toRingHom]
    rfl
  let b := splitActionOfChart J c hc
  have hB : FixesVectors B.stabilizer b (fun i => mapCoordinatesOfModel e.toRingHom (v i)) := by
    simp only [hv]
    exact cubicFixesVectors B d c hc
  let K := AlgebraicClosure F
  let C := CommAlgCat.of F K
  obtain ⟨t, ht⟩ := exists_markedChart M degree d
  let j := chartTransition J C (c C) t
  have hj : SpansDiagonal (fun i => j (mapModel (algebraMap F K)
      (mapCoordinatesOfModel e.toRingHom (v i)))) := by
    simp only [hv, show algebraMap F K = algebraMap F C from rfl, vF,
      groundCoordinates_natural J c hc, j, chartTransition_apply]
    exact ht
  obtain ⟨p, hp, hpSpan⟩ := smallTransition e v j (chartTransition_automorphism J C (c C) t) hj
  obtain ⟨I, _⟩ := Albert.AutomorphismType.automorphismType
  let L := algebraicFiber I.split k
  let a := geometricFiberAction I.split k
  obtain ⟨H, hH⟩ := exists_vectorFixingSubgroup L a v
  have hgeom := geometricConjugacyOfSpanning I.split H v hH p hp hpSpan
  obtain ⟨T, r, hr, ⟨iso⟩⟩ :=
    TrialitarianSplitTorus.trialitarianIsotropy k I.presentation I.split H hgeom
  obtain ⟨n, hn⟩ := unitsFromPositiveTorus T hr iso
  obtain ⟨s, hs, hsn⟩ := liftFixingPoints e H B.stabilizer a b v hH hB
  let q (R : TestAlgebra k) : Rˣ →* Points B.stabilizer.group.X (liftAlgebra e R) :=
    (s R).comp (n.app R).hom
  have hq {R T : TestAlgebra k} (f : R ⟶ T) (x : Rˣ) :
      mapPoints (liftAlgebraMap e f) (q R x) = q T (Units.map f.hom.toMonoidHom x) := by
    change mapPoints (liftAlgebraMap e f) (s R (n.app R x)) = s T (n.app T _)
    rw [hsn]
    exact congrArg (s T) (DFunLike.congr_fun (congrArg GrpCat.Hom.hom (n.naturality f)) x).symm
  obtain ⟨q', hq', hcomp⟩ := extendUnitFamily e B.stabilizer.group q hq
  obtain ⟨x, hx⟩ := TrialitarianSplitTorus.localField_infiniteOrderUnit k
  have hne : x ≠ 1 := fun h => hx (h ▸ by simp)
  let A := CommAlgCat.of k k
  have hnz : q' (liftAlgebra e A) (Units.map (upCoefficients A).toMonoidHom x) ≠ 1 := by
    rw [hcomp]
    intro h
    apply hne
    apply (hs A).comp (hn A)
    exact h.trans ((q A).map_one).symm
  obtain ⟨cochar, hcochar⟩ := nonzeroCocharacterOfUnits B.stabilizer.group q' hq' ⟨_, _, hnz⟩
  have hnonzero : cochar ≫ M.realization.inv ≠ 0 := by
    intro h
    apply hcochar
    have he := congrArg (· ≫ M.realization.hom) h
    simpa only [Category.assoc, Iso.inv_hom_id, Category.comp_id, zero_comp] using he
  have hpos := (positive_rank_iff_cocharacter G).2 ⟨_, hnonzero⟩
  exact proper_parabolic_cocharacter G
    ((LinearAlgebraicGroups.Descent.RelativeRank.semisimpleParabolicCriterion G hG).2 hpos)

/-- The given marked Albert model yields a noncentral cocharacter over the
local field. -/
theorem albertIsotropy :
    LinearAlgebraicGroups.Specs.Arithmetic.TrialitarianAlbertApplication.AlbertIsotropy.{u} := by
  intro F E S _ _ _ _ _ _ _ _ _ _ _ _ _ degree G D hG _ M
  exact albertIsotropyFromModel F E S degree G D hG M

end Isotropy

end

end LinearAlgebraicGroups.Arithmetic.TrialitarianAlbertApplication
