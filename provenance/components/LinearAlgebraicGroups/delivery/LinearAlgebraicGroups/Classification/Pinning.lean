import Specs.LinearAlgebraicGroups.Classification.Pinning
import LinearAlgebraicGroups.RootData.BorelsAndChambers
import LinearAlgebraicGroups.RootData.SimpleRoots
import Batteries.Tactic.OpenPrivate

open AlgebraicGeometry CategoryTheory
open scoped CategoryTheory.MonObj

universe u

namespace LinearAlgebraicGroups.Classification.Pinning

open _root_.LinearAlgebraicGroups.Specs
open Specs.Pinning
open Specs.AbstractPairing (Root)
open Specs.AdjointRepresentation (GroupPoints)
open Specs.CharacterPairing (adjointWeightVectors)
open Specs.RootGroups (AdditiveLine HasScalarAction rootPoint)
open RootData.RootGroups (additivePoints rootSubgroups)
open private additiveLineGroup additiveLinePointsIso additiveLine_tangent_point
  rootPoint_comp rootPoint_eq rootPoint_injective_of_mono rootPoint_natural rootPoint_zero
  hom_ext_on_affine_tests
  rootPoint_eps_reduces tangent_weight_of_scalarAction
  from LinearAlgebraicGroups.RootData.RootGroups
open private groupIsoOfPointIso from LinearAlgebraicGroups.Affine.IdentityTangent
open private subgroupOf_mutual_iso from LinearAlgebraicGroups.Reductive.GeometricBorelConjugacy

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

variable {k : Type u} [Field k]

private abbrev dualTest (k : Type u) [Field k] := CommAlgCat.of k (DualNumber k)

/-- A change between standard additive coordinates given by multiplication by a unit. -/
private def scalePoints (c : kˣ) :
    StandardGroups.additivePoints k ≅ StandardGroups.additivePoints k :=
  NatIso.ofComponents (fun R =>
    (show Multiplicative R ≃* Multiplicative R from
      { toFun := fun a => Multiplicative.ofAdd (algebraMap k R (c : k) * a.toAdd)
        invFun := fun a => Multiplicative.ofAdd (algebraMap k R (↑c⁻¹ : k) * a.toAdd)
        left_inv := fun a => by
          apply Multiplicative.toAdd.injective
          simp [← mul_assoc, ← map_mul]
        right_inv := fun a => by
          apply Multiplicative.toAdd.injective
          simp [← mul_assoc, ← map_mul]
        map_mul' := fun a b => by
          apply Multiplicative.toAdd.injective
          exact mul_add _ _ _ }).toGrpIso)
    (by
      intro R S f
      apply GrpCat.ext
      intro a
      change Multiplicative R at a
      apply Multiplicative.toAdd.injective
      change algebraMap k S (c : k) * f.hom a.toAdd =
        f.hom (algebraMap k R (c : k) * a.toAdd)
      rw [map_mul, AlgHom.commutes])

private def scaleIso (A B : AdditiveLine k) (c : kˣ) : A.group ≅ B.group := by
  letI := (additiveLineGroup A).property.1
  letI := (additiveLineGroup B).property.1
  exact groupIsoOfPointIso ((additiveLinePointsIso A).symm ≪≫ scalePoints c ≪≫
    additiveLinePointsIso B)

private theorem scaleIso_point (A B : AdditiveLine k) (c : kˣ) (R : TestAlgebra k) (a : R) :
    rootPoint (scaleIso A B c).hom R a =
      additivePoints B R (algebraMap k R (c : k) * a) := by
  letI := (additiveLineGroup A).property.1
  letI := (additiveLineGroup B).property.1
  have h : (groupPointsFunctor k).map (scaleIso A B c).hom =
      (((additiveLinePointsIso A).symm ≪≫ scalePoints c ≪≫ additiveLinePointsIso B)).hom :=
    (groupHomEquiv A.group B.group inferInstance).apply_symm_apply _
  have he := congrArg (fun f => (f.app R).hom (additivePoints A R a)) h
  rw [rootPoint_eq]
  change (((groupPointsFunctor k).map (scaleIso A B c).hom).app R).hom
    (additivePoints A R a) = additivePoints B R (algebraMap k R (c : k) * a)
  rw [he]
  change additivePoints B R
    (algebraMap k R (c : k) * (additivePoints A R).symm (additivePoints A R a)) = _
  rw [Equiv.symm_apply_apply]

private theorem additiveIso_polynomial (A B : AdditiveLine k) (i : A.group ≅ B.group) :
    ∃ p : Polynomial k, ∀ (R : TestAlgebra k) (a : R),
      rootPoint i.hom R a = additivePoints B R (Polynomial.aeval a p) := by
  let R₀ := CommAlgCat.of k (Polynomial k)
  obtain ⟨p, hp⟩ := (additivePoints B R₀).surjective (rootPoint i.hom R₀ Polynomial.X)
  refine ⟨p, fun R a => ?_⟩
  let f : R₀ ⟶ R := CommAlgCat.ofHom (Polynomial.aeval a)
  have h := congrArg (mapPoints f) hp
  change mapPoints f (rootPoint (𝟙 B.group) R₀ p) =
    mapPoints f (rootPoint i.hom R₀ Polynomial.X) at h
  rw [rootPoint_natural, rootPoint_natural] at h
  change rootPoint (𝟙 B.group) R ((Polynomial.aeval a) p) =
    rootPoint i.hom R ((Polynomial.aeval a) Polynomial.X) at h
  rw [Polynomial.aeval_X] at h
  exact h.symm

private theorem additiveIso_linear (A B : AdditiveLine k) (i : A.group ≅ B.group) :
    ∃ c : kˣ, ∀ (R : TestAlgebra k) (a : R),
      rootPoint i.hom R a = additivePoints B R (algebraMap k R (c : k) * a) := by
  obtain ⟨p, hp⟩ := additiveIso_polynomial A B i
  obtain ⟨q, hq⟩ := additiveIso_polynomial B A i.symm
  let R₀ := CommAlgCat.of k (Polynomial k)
  have hqp : q.comp p = Polynomial.X := by
    apply (additivePoints A R₀).injective
    have h := rootPoint_comp i.hom i.inv R₀ Polynomial.X
    rw [i.hom_inv_id, hp] at h
    rw [← rootPoint_eq i.inv] at h
    change _ = rootPoint i.symm.hom R₀ ((Polynomial.aeval Polynomial.X) p) at h
    rw [hq, Polynomial.aeval_X_left_apply] at h
    change additivePoints A R₀ Polynomial.X =
      additivePoints A R₀ ((Polynomial.aeval p : Polynomial k →ₐ[k] Polynomial k) q) at h
    rw [← Polynomial.comp_eq_aeval] at h
    exact h.symm
  have hpDegree : p.natDegree = 1 := by
    have h := congrArg Polynomial.natDegree hqp
    rw [Polynomial.natDegree_comp, Polynomial.natDegree_X] at h
    exact Nat.dvd_one.mp ⟨_, h.symm.trans (mul_comm _ _)⟩
  obtain ⟨c, hc, b, hcb⟩ := Polynomial.natDegree_eq_one.mp hpDegree
  have hzero := hp (CommAlgCat.of k k) 0
  rw [rootPoint_zero, ← rootPoint_zero (𝟙 B.group)] at hzero
  have hb : b = 0 := by
    have h := (additivePoints B (CommAlgCat.of k k)).injective hzero
    simpa [← hcb] using h.symm
  refine ⟨Units.mk0 c hc, fun R a => ?_⟩
  rw [hp, ← hcb, hb]
  congr 1
  simp

private def rescale {G : GroupScheme k} {A B : AdditiveLine k}
    {T U : ClosedSubgroup G} {α : Specs.CharacterDescent.Character T.group}
    (x : RootCoordinate B T U α) (c : kˣ) : RootCoordinate A T U α := by
  refine ⟨scaleIso A B c ≪≫ x.val, ?_⟩
  intro R t a
  have h := x.property R t (algebraMap k R (c : k) * a)
  dsimp only at h ⊢
  rw [show (scaleIso A B c ≪≫ x.val).hom ≫ U.inclusion =
    (scaleIso A B c).hom ≫ (x.val.hom ≫ U.inclusion) by simp]
  simp only [rootPoint_comp, scaleIso_point]
  simpa only [rootPoint_eq, mul_left_comm (algebraMap k R (c : k))] using h

private theorem rescale_point {G : GroupScheme k} {A B : AdditiveLine k}
    {T U : ClosedSubgroup G} {α : Specs.CharacterDescent.Character T.group}
    (x : RootCoordinate B T U α) (c : kˣ) (R : TestAlgebra k) (a : R) :
    rootPoint ((rescale (A := A) x c).val.hom ≫ U.inclusion) R a =
      rootPoint (x.val.hom ≫ U.inclusion) R (algebraMap k R (c : k) * a) := by
  change rootPoint (((scaleIso A B c).hom ≫ x.val.hom) ≫ U.inclusion) R a = _
  rw [Category.assoc, rootPoint_comp, scaleIso_point, rootPoint_eq (x.val.hom ≫ U.inclusion)]

private theorem coordinate_ext {G : GroupScheme k} {A : AdditiveLine k}
    {T U : ClosedSubgroup G} {α : Specs.CharacterDescent.Character T.group}
    (x y : RootCoordinate A T U α)
    (h : ∀ (R : TestAlgebra k) (a : R),
      rootPoint (x.val.hom ≫ U.inclusion) R a = rootPoint (y.val.hom ≫ U.inclusion) R a) :
    x = y := by
  letI := U.isClosedImmersion
  letI : Mono U.inclusion.hom.hom := Over.mono_of_mono_left _
  apply Subtype.ext
  apply Iso.ext
  apply Grp.hom_ext
  apply hom_ext_on_affine_tests
  intro R z
  obtain ⟨a, rfl⟩ := (additivePoints A R).surjective z
  have he := h R a
  rw [rootPoint_comp, rootPoint_comp, rootPoint_eq x.val.hom, rootPoint_eq y.val.hom] at he
  exact (cancel_mono U.inclusion.hom.hom).mp he

private theorem coordinate_change {G : GroupScheme k} {A : AdditiveLine k}
    {T U : ClosedSubgroup G} {α : Specs.CharacterDescent.Character T.group}
    (x y : RootCoordinate A T U α) :
    ∃ c : kˣ, y = rescale x c := by
  let i := y.val ≪≫ x.val.symm
  obtain ⟨c, hc⟩ := additiveIso_linear A A i
  refine ⟨c, coordinate_ext _ _ (fun R a => ?_)⟩
  rw [rescale_point, rootPoint_eq (x.val.hom ≫ U.inclusion), ← hc]
  rw [← rootPoint_comp, show i.hom ≫ (x.val.hom ≫ U.inclusion) = y.val.hom ≫ U.inclusion by
    simp [i]]

theorem coordinateChanges : CoordinateChanges.{u} := by
  intro k _ G A T U α x y
  obtain ⟨c, rfl⟩ := coordinate_change x y
  refine ⟨c, rescale_point x c, ?_⟩
  intro d hd
  let R := CommAlgCat.of k k
  let f := x.val.hom ≫ U.inclusion
  letI := U.isClosedImmersion
  letI : Mono U.inclusion.hom.hom := Over.mono_of_mono_left _
  letI : Mono f.hom.hom := by
    change Mono (x.val.hom.hom.hom ≫ U.inclusion.hom.hom)
    infer_instance
  have h := (hd R 1).symm.trans (rescale_point x c R 1)
  have he := rootPoint_injective_of_mono f R h
  apply Units.ext
  change (d : k) * 1 = (c : k) * 1 at he
  simpa only [mul_one] using he

private def coordinateVector {G : GroupScheme k} {A : AdditiveLine k}
    {T U : ClosedSubgroup G} {α : Specs.CharacterDescent.Character T.group}
    (x : RootCoordinate A T U α) : RootVector T α := by
  let f := x.val.hom ≫ U.inclusion
  let p : Lie k G :=
    ⟨rootPoint f (dualTest k) DualNumber.eps, rootPoint_eps_reduces f⟩
  have hp : p ∈ Set.range (mapPointKernel U.inclusion) := by
    let q : Lie k U.group :=
      ⟨rootPoint x.val.hom (dualTest k) DualNumber.eps, rootPoint_eps_reduces x.val.hom⟩
    refine ⟨q, Subtype.ext ?_⟩
    change rootPoint x.val.hom (dualTest k) DualNumber.eps ≫ U.inclusion.hom.hom = _
    exact (rootPoint_comp _ _ _ _).symm
  refine ⟨p, tangent_weight_of_scalarAction T U α A x.val x.property hp, ?_⟩
  letI := U.isClosedImmersion
  letI : Mono U.inclusion.hom.hom := Over.mono_of_mono_left _
  letI : Mono f.hom.hom := by
    change Mono (x.val.hom.hom.hom ≫ U.inclusion.hom.hom)
    infer_instance
  intro hp0
  have hz : rootPoint f (dualTest k) DualNumber.eps = rootPoint f (dualTest k) 0 :=
    (congrArg (fun v : Lie k G => v.toMul.val) hp0).trans (rootPoint_zero f _).symm
  have he := rootPoint_injective_of_mono f _ hz
  have := congrArg TrivSqZeroExt.snd he
  exact one_ne_zero this

private theorem algebraMap_mul_eps (c : k) :
    algebraMap k (DualNumber k) c * DualNumber.eps = (⟨0, c⟩ : DualNumber k) := by
  apply TrivSqZeroExt.ext
  · change c * 0 = 0
    exact mul_zero c
  · change c * 1 + 0 * 0 = c
    rw [mul_one, zero_mul, add_zero]

private theorem coord_value_rescale {G : GroupScheme k} {A : AdditiveLine k}
    {T U : ClosedSubgroup G} {α : Specs.CharacterDescent.Character T.group}
    (x : RootCoordinate A T U α) (c : kˣ) :
    (coordinateVector (rescale (A := A) x c)).val =
      scalePointKernel G (c : k) (coordinateVector x).val := by
  apply Subtype.ext
  change rootPoint ((rescale x c).val.hom ≫ U.inclusion) (dualTest k) DualNumber.eps =
    mapPoints (CommAlgCat.ofHom (dualNumberScale (c : k)))
      (rootPoint (x.val.hom ≫ U.inclusion) (dualTest k) DualNumber.eps)
  rw [rescale_point, rootPoint_natural]
  congr 1
  change algebraMap k (DualNumber k) (c : k) * DualNumber.eps =
    dualNumberScale (c : k) DualNumber.eps
  rw [algebraMap_mul_eps]
  apply TrivSqZeroExt.ext
  · rw [dualNumberScale, TrivSqZeroExt.fst_map]
    rfl
  · rw [dualNumberScale, TrivSqZeroExt.snd_map, DualNumber.snd_eps,
      LinearMap.smul_apply, LinearMap.id_apply, smul_eq_mul, mul_one]
    rfl

/-- Differentiation identifies the equivariant root coordinates with
nonzero root vectors, over the ground field in every characteristic. -/
theorem coordinateVectors : CoordinateVectors.{u} := by
  intro k _ A P α U hU
  obtain ⟨V, _, _, hV, ⟨B, i, hi⟩, hu⟩ :=
    (rootSubgroups P.G P.reductive P.T P.split P.maximal).2 α.val α.property |>.2.2
  have hVU := hu U hU
  obtain ⟨j, hj⟩ := subgroupOf_mutual_iso hVU.1 hVU.2
  let xB : RootCoordinate B P.T U α.val :=
    ⟨i ≪≫ j, by
      change HasScalarAction P.T α.val ((i.hom ≫ j.hom) ≫ U.inclusion)
      rw [Category.assoc, hj]
      exact hi⟩
  let x : RootCoordinate A P.T U α.val := rescale xB 1
  let f := x.val.hom ≫ U.inclusion
  letI := U.isClosedImmersion
  letI : Mono U.inclusion.hom.hom := Over.mono_of_mono_left _
  letI : Mono f.hom.hom := by
    change Mono (x.val.hom.hom.hom ≫ U.inclusion.hom.hom)
    infer_instance
  have hsurj : Function.Surjective (coordinateVector (A := A) (T := P.T) (U := U) (α := α.val)) := by
    intro v
    have hv : v.val ∈ Set.range (mapPointKernel V.inclusion) := by
      rw [hV]
      exact v.property.1
    obtain ⟨p, hp⟩ := hv
    obtain ⟨b, hb⟩ := additiveLine_tangent_point A x.val (mapPointKernel j.hom p)
    have hv : v.val.toMul.val = rootPoint f (dualTest k) (⟨0, b⟩ : DualNumber k) := by
      have h := congrArg (fun v : Lie k P.G.val => v.toMul.val) hp
      change p.toMul.val ≫ V.inclusion.hom.hom = _ at h
      rw [rootPoint_comp, ← hb]
      change v.val.toMul.val = (p.toMul.val ≫ j.hom.hom.hom) ≫ U.inclusion.hom.hom
      rw [Category.assoc, ← show (j.hom ≫ U.inclusion).hom.hom =
        j.hom.hom.hom ≫ U.inclusion.hom.hom from rfl, hj]
      exact h.symm
    have hb0 : b ≠ 0 := by
      intro h
      apply v.property.2
      apply Subtype.ext
      change v.val.toMul.val = 1
      rw [hv, h]
      exact rootPoint_zero f _
    refine ⟨rescale x (Units.mk0 b hb0), Subtype.ext (Subtype.ext ?_)⟩
    change rootPoint ((rescale x (Units.mk0 b hb0)).val.hom ≫ U.inclusion)
      (dualTest k) DualNumber.eps = v.val.toMul.val
    rw [rescale_point, hv]
    congr 1
    exact algebraMap_mul_eps b
  have hinj : Function.Injective (coordinateVector (A := A) (T := P.T) (U := U) (α := α.val)) := by
    intro y z h
    obtain ⟨a, rfl⟩ := coordinate_change x y
    obtain ⟨b, rfl⟩ := coordinate_change x z
    have h' := congrArg (fun v : RootVector P.T α.val => v.val.toMul.val) h
    change rootPoint ((rescale x a).val.hom ≫ U.inclusion) (dualTest k) DualNumber.eps =
      rootPoint ((rescale x b).val.hom ≫ U.inclusion) (dualTest k) DualNumber.eps at h'
    rw [rescale_point x a, rescale_point x b] at h'
    have he := rootPoint_injective_of_mono f _ h'
    change algebraMap k (DualNumber k) (a : k) * DualNumber.eps =
      algebraMap k (DualNumber k) (b : k) * DualNumber.eps at he
    rw [algebraMap_mul_eps, algebraMap_mul_eps] at he
    have hs := congrArg TrivSqZeroExt.snd he
    have hab : a = b := Units.ext hs
    rw [hab]
  refine ⟨Equiv.ofBijective coordinateVector ⟨hinj, hsurj⟩, fun _ => rfl, ?_⟩
  intro y c
  refine ⟨rescale y c, ⟨rescale_point y c, coord_value_rescale y c⟩, ?_⟩
  intro z hz
  exact coordinate_ext _ _ fun R a => (hz.1 R a).trans (rescale_point y c R a).symm

theorem pinningVectors : PinningVectors.{u} := by
  intro k _ A P U
  let h (α : SimpleRoot P) := coordinateVectors A P α.val (U α.val).val (U α.val).property
  let e (α : SimpleRoot P) := Classical.choose (h α)
  have he (α : SimpleRoot P) := Classical.choose_spec (h α)
  refine ⟨Equiv.piCongrRight e, fun x α => (he α).1 (x α), ?_⟩
  intro x c
  choose y hy hu using fun α => (he α).2 (x α) (c α)
  refine ⟨y, ⟨fun α => (hy α).1, fun α => (hy α).2⟩, ?_⟩
  intro z hz
  funext α
  exact hu α (z α) ⟨hz.1 α, hz.2 α⟩

theorem pinningsExist : PinningsExist.{u} := by
  intro k _ A P
  have h (α : Root P.T) := (rootSubgroups P.G P.reductive P.T P.split P.maximal).2
    α.val α.property
  let U : Specs.OrderedRootProducts.RootSubgroupFamily P.T := fun α =>
    ⟨Classical.choose (h α).2.2, (Classical.choose_spec (h α).2.2).1⟩
  obtain ⟨e, _⟩ := pinningVectors A P U
  have hv (α : SimpleRoot P) : Nonempty (RootVector P.T α.val.val) := by
    obtain ⟨_, v, hv, hn⟩ := α.val.property
    exact ⟨⟨v, hv, hn⟩⟩
  exact ⟨U, ⟨e.symm fun α => Classical.choice (hv α)⟩⟩

theorem additiveLineExists : AdditiveLineExists.{u} := by
  intro k _
  obtain ⟨ops, hd, he, hi, _⟩ := LinearAlgebraicGroups.StandardGroups.additiveGroupSpecification k
  exact ⟨⟨ops, hd, he, hi⟩⟩

/-- The polynomial additive group with its standard coordinate. -/
def standardAdditiveLine (k : Type u) [Field k] : AdditiveLine k :=
  Classical.choice (additiveLineExists k)

open Specs.BorelsAndChambers (positiveRoots subgroupRoots)
open Specs.CharacterDescent (Character Cocharacter compositionPairing)
open Specs.CharacterPairing (absoluteRoots characterValue pairing)
open Specs.BorelNormalizer (InducesTorusConjugation)
open Specs.AdjointRepresentation (constants dualMap scale)
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory

/-- The chosen Borel supplies exactly the positives defining the base. -/
theorem datumExists : DatumExists.{u} := by
  intro k _ P
  obtain ⟨h, ⟨D⟩⟩ :=
    RootData.AbstractPairing.abstractPairing P.G P.reductive P.T P.split P.maximal
  letI := h
  obtain ⟨c, _, hr, _, hp⟩ :=
    (RootData.BorelsAndChambers.borelsThroughT P.G P.reductive P.T P.split P.maximal).1
      P.B P.borel P.containsTorus
  letI := D.finiteRoots
  letI := D.freeCharacters
  letI := D.finiteCharacters
  letI := D.reduced
  let f := Specs.SimpleRoots.evaluate D c
  have hf (i : Root P.T) : f (D.rootDatum.root i) = pairing P.T.group i.val c := by
    change D.rootDatum.toLinearMap (D.rootDatum.root i) (Additive.ofMul c) = _
    rw [D.root_eq, D.pairing_eq]
  obtain ⟨b, hb⟩ := RootData.SimpleRoots.baseFor D.rootDatum f (fun i => hf i ▸ hr i)
  have hpos : Specs.SimpleRoots.positive D.rootDatum f = subgroupRoots P.T P.B := by
    rw [hp]
    ext i
    change 0 < f (D.rootDatum.root i) ↔ 0 < pairing P.T.group i.val c
    rw [hf]
  refine ⟨⟨h, D, b, fun α => ?_⟩⟩
  rw [hb.simple_iff, hpos]
  unfold IsSimple
  simp only [D.root_eq]
  rfl

private abbrev underlying (k : Type u) [Field k] := Grp.forget (SchemeOver k)

private theorem mapPoints_postcomp {G H : GroupScheme k} {R S : TestAlgebra k}
    (a : R ⟶ S) (p : GroupPoints G R) (f : G ⟶ H) :
    mapPoints a (p ≫ f.hom.hom) = mapPoints a p ≫ f.hom.hom :=
  (Category.assoc _ _ _).symm

private theorem torusPoint_comm {A : AdditiveLine k} {P Q : PinnedGroup A}
    (f : PinnedIso P Q) {X : SchemeOver k} (t : X ⟶ P.pair.T.group.X) :
    (t ≫ P.pair.T.inclusion.hom.hom) ≫ f.group.hom.hom.hom =
      (t ≫ f.torus.hom.hom.hom) ≫ Q.pair.T.inclusion.hom.hom := by
  simpa only [Grp.comp_hom_hom, Category.assoc] using
    congrArg (fun j : P.pair.T.group ⟶ Q.pair.G.val => t ≫ j.hom.hom) f.torus_comm

private theorem transportedWeight {A : AdditiveLine k} {P Q : PinnedGroup A}
    (f : PinnedIso P Q) {χ : Character P.pair.T.group} {v : Lie k P.pair.G.val}
    (hv : v ∈ adjointWeightVectors P.pair.T χ) :
    mapPointKernel f.group.hom v ∈ adjointWeightVectors Q.pair.T
      (transportCharacter f.torus χ) := by
  intro R t
  let s : GroupPoints P.pair.T.group R := t ≫ f.torus.inv.hom.hom
  have ht : s ≫ f.torus.hom.hom.hom = t := by
    change t ≫ f.torus.inv.hom.hom ≫ f.torus.hom.hom.hom = t
    rw [show f.torus.inv.hom.hom ≫ f.torus.hom.hom.hom = 𝟙 _ from
      ((underlying k).mapIso f.torus).inv_hom_id, Category.comp_id]
  have hχ : characterValue (transportCharacter f.torus χ) R t = characterValue χ R s := by
    unfold characterValue transportCharacter
    simp only [s, Grp.comp_hom_hom, Category.assoc]
  let a := dualMap (CommAlgCat.ofHom (Algebra.ofId k R))
  let g : GroupPoints P.pair.G.val (CommAlgCat.of k (DualNumber R)) :=
    mapPoints (constants R) (s ≫ P.pair.T.inclusion.hom.hom)
  let p : GroupPoints P.pair.G.val (CommAlgCat.of k (DualNumber R)) := mapPoints a v.toMul.val
  let d := f.group.hom.hom.hom
  have hg : mapPoints (constants R) (t ≫ Q.pair.T.inclusion.hom.hom) = g ≫ d := by
    rw [← ht, ← torusPoint_comm f s]
    exact mapPoints_postcomp _ _ _
  have hh : g * p * g⁻¹ = mapPoints (scale R (characterValue χ R s)) p := hv R s
  have h := congrArg (fun z => z ≫ d) hh
  change mapPoints (constants R) (t ≫ Q.pair.T.inclusion.hom.hom) *
    mapPoints a (v.toMul.val ≫ d) *
    (mapPoints (constants R) (t ≫ Q.pair.T.inclusion.hom.hom))⁻¹ =
      mapPoints (scale R (characterValue (transportCharacter f.torus χ) R t))
        (mapPoints a (v.toMul.val ≫ d))
  rw [hg, hχ, mapPoints_postcomp, mapPoints_postcomp]
  change (g * p * g⁻¹) ≫ d = mapPoints (scale R (characterValue χ R s)) p ≫ d at h
  dsimp only [d] at h
  rw [MonObj.mul_comp, MonObj.mul_comp, GrpObj.inv_comp] at h
  exact h

open private charactersOfIso cocharactersOfIso from LinearAlgebraicGroups.RootData.CharacterPairing

private theorem transportedRoot {A : AdditiveLine k} {P Q : PinnedGroup A} (f : PinnedIso P Q) :
    Set.MapsTo (transportCharacter f.torus) (absoluteRoots P.pair.T) (absoluteRoots Q.pair.T) := by
  rintro χ ⟨hχ, v, hv, hv₀⟩
  refine ⟨?_, mapPointKernel f.group.hom v, transportedWeight f hv, ?_⟩
  · intro he
    apply hχ
    apply (charactersOfIso f.torus).injective
    exact he.trans (map_one _).symm
  · intro he
    apply hv₀
    have h := congrArg (fun z : Lie k Q.pair.G.val => z.toMul.val) he
    change v.toMul.val ≫ f.group.hom.hom.hom = 1 at h
    rw [← MonObj.one_comp f.group.hom.hom.hom] at h
    exact Subtype.ext ((cancel_mono f.group.hom.hom.hom).mp h)

private def rootEquiv {A : AdditiveLine k} {P Q : PinnedGroup A} (f : PinnedIso P Q) :
    Root P.pair.T ≃ Root Q.pair.T where
  toFun α := ⟨transportCharacter f.torus α.val, transportedRoot f α.property⟩
  invFun α := ⟨transportCharacter f.torus.symm α.val, transportedRoot f.symm α.property⟩
  left_inv α := by apply Subtype.ext; simp [transportCharacter]
  right_inv α := by apply Subtype.ext; simp [transportCharacter]

private theorem rootEquiv_simple {A : AdditiveLine k} {P Q : PinnedGroup A} (f : PinnedIso P Q)
    (α : Root P.pair.T) (ha : IsSimple P.pair α) : IsSimple Q.pair (rootEquiv f α) := by
  let a : SimpleRoot P.pair := ⟨α, ha⟩
  have h : (transportCharacter f.torus α.val,
      (P.pin a).val.hom ≫ (P.roots α).val.inclusion ≫ f.group.hom) ∈ pinGraph Q := by
    rw [← f.pin_comm]
    exact ⟨_, ⟨a, rfl⟩, by simp [a, Category.assoc]⟩
  obtain ⟨β, hβ⟩ := h
  have he : β.val = rootEquiv f α := Subtype.ext (congrArg Prod.fst hβ)
  exact he ▸ β.property

open private reflectionConjugation inducedConjugation_unique
  from LinearAlgebraicGroups.RootData.DatumAndWeyl
open private normalizes_of_conjugates_self
  from LinearAlgebraicGroups.Reductive.MaximalToriConjugate

private theorem conjugation_transport {A : AdditiveLine k} {P Q : PinnedGroup A}
    (f : PinnedIso P Q) {g : 𝟙_ (SchemeOver k) ⟶ P.pair.G.val.X}
    {e : P.pair.T.group ≅ P.pair.T.group} (h : InducesTorusConjugation P.pair.T g e) :
    InducesTorusConjugation Q.pair.T (g ≫ f.group.hom.hom.hom) (f.torus.symm ≪≫ e ≪≫ f.torus) := by
  let b := f.torus.inv.hom.hom
  let d := f.group.hom.hom.hom
  have hb : (b ≫ f.torus.hom.hom.hom) = 𝟙 _ := ((underlying k).mapIso f.torus).inv_hom_id
  have hT := torusPoint_comm f b
  have hTe := torusPoint_comm f (b ≫ e.hom.hom.hom)
  rw [hb, Category.id_comp] at hT
  change b ≫ e.hom.hom.hom ≫ f.torus.hom.hom.hom ≫ Q.pair.T.inclusion.hom.hom = _
  calc
    _ = ((b ≫ e.hom.hom.hom) ≫ P.pair.T.inclusion.hom.hom) ≫ d := by
      simpa only [Category.assoc, d] using hTe.symm
    _ = (b ≫ ((toUnit P.pair.T.group.X ≫ g) * P.pair.T.inclusion.hom.hom *
        (toUnit P.pair.T.group.X ≫ g)⁻¹)) ≫ d := by
      have he := congrArg (fun p => (b ≫ p) ≫ d) h
      simpa only [Grp.comp_hom_hom, Category.assoc] using he
    _ = _ := by
      rw [MonObj.comp_mul, MonObj.comp_mul, GrpObj.comp_inv]
      rw [← Category.assoc b (toUnit P.pair.T.group.X), comp_toUnit]
      dsimp only [d]
      rw [MonObj.mul_comp, MonObj.mul_comp, GrpObj.inv_comp, hT, Category.assoc]

private def weightEquiv {A : AdditiveLine k} {P Q : PinnedGroup A}
    (f : PinnedIso P Q) :
    Additive (Character P.pair.T.group) ≃ₗ[ℤ] Additive (Character Q.pair.T.group) :=
  (charactersOfIso f.torus).toAdditive.toIntLinearEquiv

private def coweightEquiv {A : AdditiveLine k} {P Q : PinnedGroup A}
    (f : PinnedIso P Q) (D : AttachedDatum P.pair) (E : AttachedDatum Q.pair) :
    letI := D.comm
    letI := E.comm
    Additive (Cocharacter Q.pair.T.group) ≃ₗ[ℤ] Additive (Cocharacter P.pair.T.group) :=
  letI := D.comm
  letI := E.comm
  (cocharactersOfIso f.torus.symm).toAdditive.toIntLinearEquiv

private theorem pairing_transport {A : AdditiveLine k} {P Q : PinnedGroup A}
    (f : PinnedIso P Q) (χ : Character P.pair.T.group) (c : Cocharacter Q.pair.T.group) :
    pairing Q.pair.T.group (transportCharacter f.torus χ) c =
      pairing P.pair.T.group χ (c ≫ f.torus.inv) := by
  unfold pairing compositionPairing transportCharacter
  rw [Category.assoc]

/-- A normalizer automorphism which reverses the root and whose displacement
is along that root has the indicated coroot functional, on the full lattice. -/
private theorem coroot_functional_of_reflection {I X Y : Type u}
    [AddCommGroup X] [AddCommGroup Y] (D : RootDatum I X Y)
    (j : I) (a : D.Aut) (p : X →ₗ[ℤ] ℤ)
    (hp : p (D.root j) = 2)
    (ha : ∀ x, a.weightEquiv x = x - p x • D.root j) :
    D.toLinearMap.flip (D.coroot j) = p := by
  let i := a.indexEquiv j
  have hi : D.root i = -D.root j := by
    have hr := a.toHom.root_weightMap_apply D D j
    change a.weightEquiv (D.root j) = D.root i at hr
    rw [ha, hp, two_smul, sub_add_cancel_left] at hr
    exact hr.symm
  have hci : D.coroot i = -D.coroot j :=
    (D.coroot_eq_neg_iff).mpr ((D.root_eq_neg_iff).mp hi)
  have hc := a.toHom.coroot_coweightMap_apply D D i
  change a.toHom.coweightMap (D.coroot i) = D.coroot (a.indexEquiv.symm (a.indexEquiv j)) at hc
  rw [Equiv.symm_apply_apply] at hc
  ext x
  have h := DFunLike.congr_fun
    (a.toHom.weight_coweight_transpose_apply D D (D.coroot i)) x
  change D.toLinearMap (a.weightEquiv x) (D.coroot i) =
    D.toLinearMap x (a.toHom.coweightMap (D.coroot i)) at h
  rw [hc, hci, ha, map_neg, map_sub, LinearMap.sub_apply, map_smul, LinearMap.smul_apply,
    D.root_coroot_eq_pairing, D.pairing_same, smul_eq_mul] at h
  change D.toLinearMap x (D.coroot j) = p x
  omega

private theorem coroot_transport {A : AdditiveLine k} {P Q : PinnedGroup A}
    (f : PinnedIso P Q) (D : AttachedDatum P.pair) (E : AttachedDatum Q.pair)
    (i : Root P.pair.T) :
    letI := D.comm
    letI := E.comm
    coweightEquiv f D E (E.datum.rootDatum.coroot (rootEquiv f i)) =
      D.datum.rootDatum.coroot i := by
  letI := D.comm
  letI := E.comm
  let L := weightEquiv f
  let j := rootEquiv f i
  let p : Additive (Character Q.pair.T.group) →ₗ[ℤ] ℤ :=
    (D.datum.rootDatum.toLinearMap.flip (D.datum.rootDatum.coroot i)).comp L.symm.toLinearMap
  have hroot : L (D.datum.rootDatum.root i) = E.datum.rootDatum.root j := by
    rw [D.datum.root_eq, E.datum.root_eq]
    rfl
  have hp : p (E.datum.rootDatum.root j) = 2 := by
    change D.datum.rootDatum.toLinearMap (L.symm (E.datum.rootDatum.root j)) _ = 2
    rw [← hroot, L.symm_apply_apply, RootPairing.root_coroot_eq_pairing, RootPairing.pairing_same]
  obtain ⟨g, _, e, he, hRef⟩ := reflectionConjugation D.datum i
  let g' := g ≫ f.group.hom.hom.hom
  let e' := f.torus.symm ≪≫ e ≪≫ f.torus
  have he' : InducesTorusConjugation Q.pair.T g' e' := conjugation_transport f he
  obtain ⟨N, hN, act, hact⟩ := E.datum.normalizerAction
  obtain ⟨n, hn⟩ := (hN _ g').mp (normalizes_of_conjugates_self Q.pair.T ⟨e', he'⟩)
  obtain ⟨b, hb, hbW, _⟩ := hact n
  have hb' : InducesTorusConjugation Q.pair.T g' b := by
    unfold InducesTorusConjugation
    simpa only [← Category.assoc, hn, Category.assoc] using hb
  have hbe := inducedConjugation_unique hb' he'
  have hW (x : Additive (Character Q.pair.T.group)) :
      (act n).weightEquiv x = x - p x • E.datum.rootDatum.root j := by
    obtain ⟨χ, rfl⟩ := L.surjective x
    let ψ := Additive.toMul χ
    have hcomp :
        (act n).weightEquiv (L χ) =
          L ((RootPairing.Equiv.reflection D.datum.rootDatum i).weightEquiv χ) := by
      change (act n).weightEquiv (Additive.ofMul (f.torus.inv ≫ ψ)) =
         L ((RootPairing.Equiv.reflection D.datum.rootDatum i).weightEquiv
           (Additive.ofMul ψ))
      rw [hbW, hbe, hRef]
      change Additive.ofMul ((f.torus.inv ≫ e.inv ≫ f.torus.hom) ≫ f.torus.inv ≫ ψ) =
        Additive.ofMul (f.torus.inv ≫ e.inv ≫ ψ)
      simp only [Category.assoc, Iso.hom_inv_id_assoc]
    rw [hcomp, RootPairing.Equiv.reflection_weightEquiv, RootPairing.reflection_apply]
    change L.toLinearMap (χ - D.datum.rootDatum.coroot' i χ • D.datum.rootDatum.root i) = _
    rw [map_sub L.toLinearMap, map_smul L.toLinearMap,
      show L.toLinearMap (D.datum.rootDatum.root i) = _ from hroot]
    change L χ - D.datum.rootDatum.coroot' i χ • E.datum.rootDatum.root j =
      L χ - D.datum.rootDatum.coroot' i (L.symm (L χ)) • E.datum.rootDatum.root j
    rw [L.symm_apply_apply]
  have hpE := coroot_functional_of_reflection E.datum.rootDatum j (act n) p hp hW
  apply D.datum.rootDatum.flip.toPerfPair.injective
  ext x
  let c := Additive.toMul (E.datum.rootDatum.coroot j)
  let χ := Additive.toMul x
  change D.datum.rootDatum.toLinearMap x (Additive.ofMul (c ≫ f.torus.inv)) =
    D.datum.rootDatum.toLinearMap x (D.datum.rootDatum.coroot i)
  calc
    _ = pairing P.pair.T.group χ (c ≫ f.torus.inv) := D.datum.pairing_eq χ _
    _ = pairing Q.pair.T.group (transportCharacter f.torus χ) c := (pairing_transport f χ c).symm
    _ = E.datum.rootDatum.toLinearMap.flip (E.datum.rootDatum.coroot j) (L x) :=
      (E.datum.pairing_eq (transportCharacter f.torus χ) c).symm
    _ = p (L x) := DFunLike.congr_fun hpE (L x)
    _ = _ := by
      change D.datum.rootDatum.toLinearMap (L.symm (L x)) _ = _
      rw [L.symm_apply_apply]

/-- Transport the based root datum through an isomorphism of pinned groups,
with the inverse pullback on characters and its transpose on cocharacters. -/
def inducedBasedIso {A : AdditiveLine k} {P Q : PinnedGroup A}
    (f : PinnedIso P Q) (D : AttachedDatum P.pair) (E : AttachedDatum Q.pair) :
    BasedIso D.toBased E.toBased := by
  letI := D.comm
  letI := E.comm
  let L := weightEquiv f
  let M := coweightEquiv f D E
  let e := rootEquiv f
  refine ⟨{
    weightMap := L.toLinearMap
    coweightMap := M.toLinearMap
    indexEquiv := e
    bijective_weightMap := L.bijective
    bijective_coweightMap := M.bijective
    weight_coweight_transpose := ?_
    root_weightMap := ?_
    coroot_coweightMap := ?_ }, ?_⟩
  · ext c χ
    change E.datum.rootDatum.toLinearMap (L χ) c = D.datum.rootDatum.toLinearMap χ (M c)
    exact (E.datum.pairing_eq (transportCharacter f.torus (Additive.toMul χ)) (Additive.toMul c)).trans
      ((pairing_transport f _ _).trans
        (D.datum.pairing_eq (Additive.toMul χ) (Additive.toMul c ≫ f.torus.inv)).symm)
  · funext i
    change L (D.datum.rootDatum.root i) = E.datum.rootDatum.root (e i)
    rw [D.datum.root_eq, E.datum.root_eq]
    rfl
  · funext j
    obtain ⟨i, rfl⟩ := e.surjective j
    change M (E.datum.rootDatum.coroot (e i)) = D.datum.rootDatum.coroot (e.symm (e i))
    rw [e.symm_apply_apply]
    exact coroot_transport f D E i
  · ext j
    constructor
    · rintro ⟨i, hi, rfl⟩
      exact (E.simple_iff _).mpr (rootEquiv_simple f _ ((D.simple_iff i).mp hi))
    · intro hj
      refine ⟨e.symm j, (D.simple_iff _).mpr ?_, e.apply_symm_apply j⟩
      exact rootEquiv_simple f.symm j ((E.simple_iff _).mp hj)

/-- The based datum attached to a split Borel pair. -/
def attachedDatum (P : SplitBorelPair k) : AttachedDatum P :=
  Classical.choice (datumExists P)

/-- The functor on pinned isomorphisms is inverse pullback on characters
and the dual map on the cocharacter lattice. -/
def basedDatumFunctor (A : AdditiveLine k) : PinnedGroup A ⥤ BasedRootDatum.{u} where
  obj P := (attachedDatum P.pair).toBased
  map f := inducedBasedIso f _ _
  map_id P := by
    apply Subtype.ext
    apply RootPairing.Equiv.ext
    · ext x
      change Additive.ofMul (𝟙 _ ≫ Additive.toMul x) = x
      rw [Category.id_comp]
      rfl
    · ext x
      change Additive.ofMul (Additive.toMul x ≫ 𝟙 _) = x
      rw [Category.comp_id]
      rfl
    · apply Equiv.ext
      intro x
      apply Subtype.ext
      change 𝟙 _ ≫ x.val = x.val
      exact Category.id_comp _
  map_comp f g := by
    apply Subtype.ext
    apply RootPairing.Equiv.ext
    · ext x
      change Additive.ofMul ((g.torus.inv ≫ f.torus.inv) ≫ Additive.toMul x) =
        Additive.ofMul (g.torus.inv ≫ f.torus.inv ≫ Additive.toMul x)
      rw [Category.assoc]
    · ext x
      change Additive.ofMul (Additive.toMul x ≫ (g.torus.inv ≫ f.torus.inv)) =
        Additive.ofMul ((Additive.toMul x ≫ g.torus.inv) ≫ f.torus.inv)
      rw [Category.assoc]
    · apply Equiv.ext
      intro x
      apply Subtype.ext
      exact Category.assoc g.torus.inv f.torus.inv x.val

theorem basedDatumFunctor_exists : BasedDatumFunctorExists.{u} := by
  intro k _ A
  exact ⟨fun P => attachedDatum P.pair, basedDatumFunctor A, fun _ => rfl,
    fun _ _ _ => ⟨fun _ => rfl, fun _ => rfl⟩⟩

/-- A pinning of a split Borel pair is a family of equivariant simple-root coordinates. -/
abbrev Pinning : PinningType.{u} := Specs.Pinning.Pinning

/-- The groupoid of split connected reductive groups with specified pinnings. -/
abbrev pinnedGroupoid : PinnedGroupoidType.{u} := Specs.Pinning.pinnedGroupoid

/-- The groupoid of finite based reduced root data. -/
abbrev basedRootDatumGroupoid : BasedRootDatumGroupoidType.{u} :=
  Specs.Pinning.basedRootDatumGroupoid

end

end LinearAlgebraicGroups.Classification.Pinning
