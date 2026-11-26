import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Arithmetic.F4RealCompletionCartan
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Affine.GroupSchemes
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Reductive.CocharacterLimitSubgroups
import Mathlib.Algebra.Category.CommAlgCat.FiniteType
import Batteries.Tactic.OpenPrivate

open AlgebraicGeometry CategoryTheory Opposite
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

universe u v

namespace LinearAlgebraicGroups.Arithmetic.F4RealCompletionCartan

open LinearAlgebraicGroups.Specs
open Specs.Arithmetic.F4RealCompletionCartan
open Specs.AdjointRepresentation (GroupPoints dualMap constants reduction scale)
open Specs.AbstractPairing (Root)
open Specs.BorelsAndChambers (subgroupRoots)
open Specs.CharacterDescent (Character)
open Specs.CharacterPairing (characterValue adjointWeightVectors absoluteRoots)
open Specs.DiagonalizableGroups (integerGenerator)
open InfinitesimalCommutator (mapCoefficients)
open Specs.Pinning (SplitBorelPair AttachedDatum IsSimple)
open CocharacterDynamics (mapPoints_comp lieImage unitPoint unitCoordinates mapPoints_unitPoint)

open private gm unitEquiv unitEquiv_unitPoint from
  MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Reductive.CocharacterLimitSubgroups

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false

variable {F : Type u} [Field F] {K : Type} [Field K]
variable {e : F ≃+* K} {L : TestAlgebra K ⥤ TestAlgebra F} {r : ∀ R, L.obj R ≃+* R}

private def fullyFaithful (h : AlgebraCompatible e L r) : L.FullyFaithful where
  preimage {R S} f := CommAlgCat.ofHom
    { toRingHom := ((r S).toRingHom.comp f.hom.toRingHom).comp (r R).symm.toRingHom
      commutes' := fun x => by
        change r S (f.hom ((r R).symm (algebraMap K R x))) = algebraMap K S x
        have hx (R : TestAlgebra K) :
            r R (algebraMap F (L.obj R) (e.symm x)) = algebraMap K R x := by
          rw [h.1, e.apply_symm_apply]
        rw [← hx R, (r R).symm_apply_apply, f.hom.commutes, hx S] }
  map_preimage {R S} f := by
    apply CommAlgCat.hom_ext
    apply AlgHom.ext
    intro x
    apply (r S).injective
    rw [h.2]
    change r S (f.hom ((r R).symm (r R x))) = _
    rw [(r R).symm_apply_apply]
  preimage_map {R S} f := by
    apply CommAlgCat.hom_ext
    exact AlgHom.ext fun x => (h.2 f _).trans (congrArg f.hom ((r R).apply_symm_apply x))

private theorem smallRepresentative (h : AlgebraCompatible e L r)
    (A : TestAlgebra F) (hA : Algebra.FiniteType F A) :
    ∃ R : TestAlgebra K, Nonempty (L.obj R ≅ A) := by
  have hF : (algebraMap F A).FiniteType := RingHom.finiteType_algebraMap.mpr hA
  have hK : ((algebraMap F A).comp e.symm.toRingHom).FiniteType :=
    hF.comp (RingHom.FiniteType.of_surjective _ e.symm.surjective)
  obtain ⟨P, s, hs⟩ := hK.exists_smallRepr
  let R := P.eval.obj
  let a : L.obj R ≃ₐ[F] A := AlgEquiv.ofRingEquiv (f := (r R).trans s) (fun x => by
    have hx := DFunLike.congr_fun hs (e x)
    change algebraMap F A (e.symm (e x)) = s (algebraMap K R (e x)) at hx
    change s (r R (algebraMap F (L.obj R) x)) = _
    rw [h.1, ← hx, e.symm_apply_apply])
  exact ⟨R, ⟨CommAlgCat.isoMk a⟩⟩

private theorem spectrumPresentation (h : AlgebraCompatible e L r)
    (X : SchemeOver F) [IsAffine X.left] [LocallyOfFiniteType X.hom] :
    ∃ R : TestAlgebra K, Nonempty ((testSpec F).obj (op (L.obj R)) ≅ X) := by
  obtain ⟨A, ⟨z⟩⟩ := AlgebraicGeometry.essImage_algSpec.mpr (inferInstance : IsAffine X.left)
  have hf : LocallyOfFiniteType ((testSpec F).obj A).hom := by
    rw [← Over.w z.hom]
    have : IsIso z.hom.left := (Over.forget _).map_isIso z.hom
    infer_instance
  have hA : Algebra.FiniteType F A.unop := by
    apply RingHom.finiteType_algebraMap.mp
    exact (HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)
      (φ := CommRingCat.ofHom (algebraMap F A.unop))).mp hf
  obtain ⟨R, ⟨j⟩⟩ := smallRepresentative h A.unop hA
  exact ⟨R, ⟨(testSpec F).mapIso j.op.symm ≪≫ z⟩⟩

private theorem point_factor {k : Type*} [Field k] {X : SchemeOver k} {A B : TestAlgebra k}
    (z : (testSpec k).obj (op A) ≅ X) (p : Points X B) :
    ∃ a : A ⟶ B, p = mapPoints a z.hom := by
  let ff := algSpec.fullyFaithful (R := CommRingCat.of k)
  let a := (ff.preimage (p ≫ z.inv)).unop
  refine ⟨a, ?_⟩
  change p = (testSpec k).map a.op ≫ z.hom
  have ha : (testSpec k).map a.op = p ≫ z.inv := ff.map_preimage _
  rw [ha, Category.assoc, Iso.inv_hom_id, Category.comp_id]

private theorem restrictedPoints_ext (h : AlgebraCompatible e L r)
    {X Y : SchemeOver F} [IsAffine X.left] [LocallyOfFiniteType X.hom] {f g : X ⟶ Y}
    (hf : ∀ R : TestAlgebra K, ∀ p : Points X (L.obj R), p ≫ f = p ≫ g) : f = g := by
  obtain ⟨R, ⟨z⟩⟩ := spectrumPresentation h X
  exact (cancel_epi z.hom).mp (hf R z.hom)

private abbrev pointHom {k : Type*} [Field k] {G H : GroupScheme k}
    (f : G ⟶ H) (R : TestAlgebra k) : GroupPoints G R →* GroupPoints H R :=
  (((groupPointsFunctor k).map f).app R).hom

private theorem representRestrictedHom (h : AlgebraCompatible e L r) {X Y : GroupScheme F}
    [IsAffine X.X.left] [LocallyOfFiniteType X.X.hom]
    (a : ∀ R : TestAlgebra K, GroupPoints X (L.obj R) →* GroupPoints Y (L.obj R))
    (ha : ∀ {R S : TestAlgebra K} (f : R ⟶ S) x,
      a S (mapPoints (L.map f) x) = mapPoints (L.map f) (a R x)) :
    ∃ f : X ⟶ Y, ∀ R x, pointHom f (L.obj R) x = a R x := by
  obtain ⟨R₀, ⟨z⟩⟩ := spectrumPresentation h X.X
  let t : Points Y.X (L.obj R₀) := a R₀ z.hom
  let f := z.inv ≫ t
  have hf (R : TestAlgebra K) (p : Points X.X (L.obj R)) : a R p = p ≫ f := by
    obtain ⟨c, hc⟩ := point_factor z p
    let b := (fullyFaithful h).preimage c
    have hb : L.map b = c := (fullyFaithful h).map_preimage c
    have hh := ha b z.hom
    rw [hb, ← hc] at hh
    simpa only [hc, mapPoints, f, Category.assoc, Iso.hom_inv_id_assoc] using hh
  have hmul (R : TestAlgebra K) (p q : Points X.X (L.obj R)) :
      (p * q) ≫ f = (p ≫ f) * (q ≫ f) := by
    rw [← hf, ← hf, ← hf]
    exact (a R).map_mul p q
  haveI : IsMonHom f := by
    constructor
    · haveI : IsAffine ((𝟙_ (SchemeOver F)).left) :=
        inferInstanceAs (IsAffine (Spec (CommRingCat.of F)))
      haveI : LocallyOfFiniteType ((𝟙_ (SchemeOver F)).hom) :=
        inferInstanceAs (LocallyOfFiniteType (𝟙 (Spec (CommRingCat.of F))))
      apply restrictedPoints_ext h
      intro R p
      rw [show p = toUnit _ from toUnit_unique _ _]
      change (1 : Points X.X (L.obj R)) ≫ f = 1
      rw [← hf]
      exact (a R).map_one
    · haveI : IsAffine (X.X ⊗ X.X).left := by
        change IsAffine (Limits.pullback X.X.hom X.X.hom)
        infer_instance
      haveI : LocallyOfFiniteType (X.X ⊗ X.X).hom := by
        change LocallyOfFiniteType (Limits.pullback.fst X.X.hom X.X.hom ≫ X.X.hom)
        infer_instance
      apply restrictedPoints_ext h
      intro R p
      let x := p ≫ fst X.X X.X
      let y := p ≫ snd X.X X.X
      calc
        p ≫ μ[X.X] ≫ f = (x * y) ≫ f := by
          simp only [x, y, Hom.mul_def, lift_comp_fst_snd, Category.assoc]
        _ = (x ≫ f) * (y ≫ f) := hmul R x y
        _ = p ≫ (f ⊗ₘ f) ≫ μ[Y.X] := by
          have hxy : lift (x ≫ f) (y ≫ f) = p ≫ (f ⊗ₘ f) := by
            apply CartesianMonoidalCategory.hom_ext
            · simp only [x, lift_fst, Category.assoc, tensorHom_fst]
            · simp only [y, lift_snd, Category.assoc, tensorHom_snd]
          simp only [Hom.mul_def, hxy, Category.assoc]
  exact ⟨Grp.homMk f, fun R p => (hf R p).symm⟩

private def gmCompare (r : ∀ R : TestAlgebra K, L.obj R ≃+* R) :
    PointComparison L (gm F) (gm K) :=
  fun R => (unitEquiv R).trans
    ((Units.mapEquiv (r R).symm.toMulEquiv).trans (unitEquiv (L.obj R)).symm)

private theorem unitEquiv_natural {k : Type*} [Field k] {R S : TestAlgebra k}
    (a : R ⟶ S) (p : GroupPoints (gm k) R) :
    unitEquiv S (mapPoints a p) = Units.map a.hom.toMonoidHom (unitEquiv R p) := by
  obtain ⟨x, rfl⟩ : ∃ x : Rˣ, unitPoint R x = p :=
    ⟨unitEquiv R p, (unitEquiv R).injective (unitEquiv_unitPoint _ _)⟩
  rw [mapPoints_unitPoint, unitEquiv_unitPoint, unitEquiv_unitPoint]

private theorem gmCompare_unit (R : TestAlgebra K) (p : GroupPoints (gm K) R) :
    unitEquiv (L.obj R) (gmCompare r R p) =
      Units.mapEquiv (r R).symm.toMulEquiv (unitEquiv R p) :=
  (unitEquiv (L.obj R)).apply_symm_apply _

private theorem gmCompare_natural (h : AlgebraCompatible e L r) : IsNatural (gmCompare r) := by
  intro R S a p
  apply (unitEquiv (L.obj S)).injective
  rw [gmCompare_unit, unitEquiv_natural, unitEquiv_natural, gmCompare_unit]
  apply Units.ext
  apply (r S).injective
  change r S ((r S).symm (a.hom (unitEquiv R p : R))) =
    r S ((L.map a).hom ((r R).symm (unitEquiv R p : R)))
  rw [h.2, (r S).apply_symm_apply, (r R).apply_symm_apply]

private theorem characterValue_eq_unit {k : Type*} [Field k] {X : GroupScheme k}
    (χ : Character X) (R : TestAlgebra k) (p : GroupPoints X R) :
    characterValue χ R p = (unitEquiv R (pointHom χ R p) : R) := by
  obtain ⟨x, hx⟩ : ∃ x : Rˣ, unitPoint R x = pointHom χ R p :=
    ⟨unitEquiv R (pointHom χ R p), (unitEquiv R).injective (unitEquiv_unitPoint _ _)⟩
  unfold characterValue
  dsimp only
  change ((algSpec.fullyFaithful (R := CommRingCat.of k)).preimage
    (pointHom χ R p)).unop.hom _ = _
  rw [← hx, unitEquiv_unitPoint]
  unfold unitPoint
  rw [Functor.FullyFaithful.preimage_map]
  change unitCoordinates R x (MonoidAlgebra.single integerGenerator 1) = _
  rw [unitCoordinates, MonoidAlgebra.lift_single, one_smul]
  change (x ^ (1 : ℤ) : Rˣ).val = x.val
  rw [zpow_one]

private theorem pointHom_natural {k : Type*} [Field k] {X Y : GroupScheme k}
    (f : X ⟶ Y) {R S : TestAlgebra k} (a : R ⟶ S) (p : GroupPoints X R) :
    pointHom f S (mapPoints a p) = mapPoints a (pointHom f R p) := by
  change ((testSpec k).map a.op ≫ p) ≫ f.hom.hom =
    (testSpec k).map a.op ≫ p ≫ f.hom.hom
  exact Category.assoc ..

private theorem characterValue_natural {k : Type*} [Field k] {X : GroupScheme k}
    (χ : Character X) {R S : TestAlgebra k} (a : R ⟶ S) (p : GroupPoints X R) :
    characterValue χ S (mapPoints a p) = a.hom (characterValue χ R p) := by
  rw [characterValue_eq_unit, characterValue_eq_unit, pointHom_natural, unitEquiv_natural]
  rfl

private theorem pointHom_mul_char {k : Type*} [Field k] {X : GroupScheme k}
    (χ ψ : Character X) (R : TestAlgebra k) (p : GroupPoints X R) :
    pointHom (χ * ψ) R p = pointHom χ R p * pointHom ψ R p := by
  change p ≫ (χ.hom.hom * ψ.hom.hom) = (p ≫ χ.hom.hom) * (p ≫ ψ.hom.hom)
  exact MonObj.comp_mul ..

section Characters

variable {X : GroupScheme F} {Y : GroupScheme K}
variable [IsAffine X.X.left] [LocallyOfFiniteType X.X.hom] [IsAffine Y.X.left]
variable (h : AlgebraCompatible e L r) (p : PointComparison L X Y) (hp : IsNatural p)

private def agrees (r : ∀ R : TestAlgebra K, L.obj R ≃+* R) (p : PointComparison L X Y)
    (χ : Character Y) (ψ : Character X) : Prop :=
  ∀ R x, pointHom ψ (L.obj R) (p R x) = gmCompare r R (pointHom χ R x)

omit [IsAffine Y.X.left] in
include h hp in
private theorem agrees_exists (χ : Character Y) : ∃ ψ, agrees r p χ ψ := by
  have hinv {R S : TestAlgebra K} (f : R ⟶ S) (x : GroupPoints X (L.obj R)) :
      (p S).symm (mapPoints (L.map f) x) = mapPoints f ((p R).symm x) := by
    apply (p S).injective
    rw [MulEquiv.apply_symm_apply, hp, MulEquiv.apply_symm_apply]
  let a (R : TestAlgebra K) := (gmCompare r R).toMonoidHom.comp
    ((pointHom χ R).comp (p R).symm.toMonoidHom)
  obtain ⟨ψ, hψ⟩ := representRestrictedHom h a (by
    intro R S f x
    change gmCompare r S (pointHom χ S ((p S).symm (mapPoints (L.map f) x))) =
      mapPoints (L.map f) (gmCompare r R (pointHom χ R ((p R).symm x)))
    rw [hinv, pointHom_natural, gmCompare_natural h])
  refine ⟨ψ, fun R x => (hψ R (p R x)).trans ?_⟩
  change gmCompare r R (pointHom χ R ((p R).symm (p R x))) = _
  rw [MulEquiv.symm_apply_apply]

omit [IsAffine X.X.left] [LocallyOfFiniteType X.X.hom] in
include h hp in
private theorem agrees_exists_reverse (ψ : Character X) : ∃ χ, agrees r p χ ψ := by
  let a : (groupPointsFunctor K).obj Y ⟶ (groupPointsFunctor K).obj (gm K) :=
    { app := fun R => GrpCat.ofHom ((gmCompare r R).symm.toMonoidHom.comp
        ((pointHom ψ (L.obj R)).comp (p R).toMonoidHom))
      naturality := by
        intro R S f
        apply GrpCat.ext
        intro x
        apply (gmCompare r S).injective
        change gmCompare r S ((gmCompare r S).symm (pointHom ψ (L.obj S) (p S (mapPoints f x)))) =
          gmCompare r S (mapPoints f ((gmCompare r R).symm (pointHom ψ (L.obj R) (p R x))))
        rw [MulEquiv.apply_symm_apply, gmCompare_natural h, MulEquiv.apply_symm_apply,
          hp, pointHom_natural] }
  obtain ⟨χ, hχ⟩ := (groupHomComparison K Y (gm K) inferInstance).2 a
  refine ⟨χ, fun R x => ?_⟩
  have he := congrArg (fun α => (α.app R).hom x) hχ
  change pointHom χ R x = (gmCompare r R).symm (pointHom ψ (L.obj R) (p R x)) at he
  rw [he, MulEquiv.apply_symm_apply]

omit [IsAffine Y.X.left] in
include h in
private theorem agrees_unique {χ : Character Y} {ψ ψ' : Character X}
    (hψ : agrees r p χ ψ) (hψ' : agrees r p χ ψ') : ψ = ψ' := by
  apply Grp.hom_ext
  apply restrictedPoints_ext h
  intro R x
  obtain ⟨y, rfl⟩ := (p R).surjective x
  exact (hψ R y).trans (hψ' R y).symm

omit [IsAffine X.X.left] [LocallyOfFiniteType X.X.hom] in
private theorem agrees_unique_reverse {χ χ' : Character Y} {ψ : Character X}
    (hχ : agrees r p χ ψ) (hχ' : agrees r p χ' ψ) : χ = χ' := by
  apply (groupHomComparison K Y (gm K) inferInstance).1
  ext R x
  exact (gmCompare r R).injective ((hχ R x).symm.trans (hχ' R x))

private def characters : Character Y ≃* Character X where
  toFun χ := (agrees_exists h p hp χ).choose
  invFun ψ := (agrees_exists_reverse h p hp ψ).choose
  left_inv χ := agrees_unique_reverse p
    (agrees_exists_reverse h p hp ((agrees_exists h p hp χ).choose)).choose_spec
    (agrees_exists h p hp χ).choose_spec
  right_inv ψ := agrees_unique h p
    (agrees_exists h p hp ((agrees_exists_reverse h p hp ψ).choose)).choose_spec
    (agrees_exists_reverse h p hp ψ).choose_spec
  map_mul' χ ψ := by
    apply agrees_unique h p (agrees_exists h p hp (χ * ψ)).choose_spec
    intro R x
    rw [pointHom_mul_char, pointHom_mul_char, map_mul,
      (agrees_exists h p hp χ).choose_spec R x, (agrees_exists h p hp ψ).choose_spec R x]

private theorem characters_value (χ : Character Y) (R : TestAlgebra K) (x : GroupPoints Y R) :
    r R (characterValue (characters h p hp χ) (L.obj R) (p R x)) = characterValue χ R x := by
  rw [characterValue_eq_unit, characterValue_eq_unit]
  have hm := (agrees_exists h p hp χ).choose_spec R x
  change pointHom (characters h p hp χ) (L.obj R) (p R x) = _ at hm
  rw [hm, gmCompare_unit]
  exact (r R).apply_symm_apply _

end Characters

section DualNumbers

private abbrev DA {k : Type*} [Field k] (R : TestAlgebra k) :=
  CommAlgCat.of k (DualNumber R)

private def baseIso (h : AlgebraCompatible e L r) :
    L.obj (CommAlgCat.of K K) ≅ CommAlgCat.of F F :=
  CommAlgCat.isoMk (AlgEquiv.ofRingEquiv
    (f := (r (CommAlgCat.of K K)).trans e.symm) (fun x => by
      change e.symm (r (CommAlgCat.of K K) (algebraMap F _ x)) = x
      rw [h.1]
      exact e.symm_apply_apply x))

private def dualRingEquiv (R : TestAlgebra K) : L.obj (DA R) ≃+* DA (L.obj R) :=
  (r (DA R)).trans {
    __ := mapCoefficients (r R).symm.toRingHom
    invFun := mapCoefficients (r R).toRingHom
    left_inv := fun z => TrivSqZeroExt.ext ((r R).apply_symm_apply z.fst)
      ((r R).apply_symm_apply z.snd)
    right_inv := fun z => TrivSqZeroExt.ext ((r R).symm_apply_apply z.fst)
      ((r R).symm_apply_apply z.snd) }

private def dualIso (h : AlgebraCompatible e L r) (R : TestAlgebra K) :
    L.obj (DA R) ≅ DA (L.obj R) :=
  CommAlgCat.isoMk (AlgEquiv.ofRingEquiv (f := dualRingEquiv (r := r) R) (fun x => by
    change mapCoefficients (r R).symm.toRingHom
      (r (DA R) (algebraMap F (L.obj (DA R)) x)) = algebraMap F (DA (L.obj R)) x
    rw [h.1]
    apply TrivSqZeroExt.ext
    · exact (r R).symm_apply_eq.mpr (h.1 R x).symm
    · exact map_zero (r R).symm))

private theorem dualIso_fst (h : AlgebraCompatible e L r) (R : TestAlgebra K) (z : L.obj (DA R)) :
    (((dualIso h R).hom.hom z : DA (L.obj R)) : DualNumber (L.obj R)).fst =
      (r R).symm ((r (DA R) z : DualNumber R).fst) := rfl

private theorem dualIso_snd (h : AlgebraCompatible e L r) (R : TestAlgebra K) (z : L.obj (DA R)) :
    (((dualIso h R).hom.hom z : DA (L.obj R)) : DualNumber (L.obj R)).snd =
      (r R).symm ((r (DA R) z : DualNumber R).snd) := rfl

private theorem dualIso_dualMap (h : AlgebraCompatible e L r) {R S : TestAlgebra K}
    (a : R ⟶ S) :
    L.map (dualMap a) ≫ (dualIso h S).hom = (dualIso h R).hom ≫ dualMap (L.map a) := by
  apply CommAlgCat.hom_ext
  apply AlgHom.ext
  intro z
  apply TrivSqZeroExt.ext
  · change ((dualIso h S).hom.hom ((L.map (dualMap a)).hom z)).fst =
      (L.map a).hom (((dualIso h R).hom.hom z).fst)
    rw [dualIso_fst, dualIso_fst, h.2]
    apply (r S).injective
    rw [h.2, (r R).apply_symm_apply, (r S).apply_symm_apply]
    rfl
  · change ((dualIso h S).hom.hom ((L.map (dualMap a)).hom z)).snd =
      (L.map a).hom (((dualIso h R).hom.hom z).snd)
    rw [dualIso_snd, dualIso_snd, h.2]
    apply (r S).injective
    rw [h.2, (r R).apply_symm_apply, (r S).apply_symm_apply]
    rfl

private theorem dualIso_reduction (h : AlgebraCompatible e L r) (R : TestAlgebra K) :
    (dualIso h R).hom ≫ reduction (L.obj R) = L.map (reduction R) := by
  apply CommAlgCat.hom_ext
  apply AlgHom.ext
  intro z
  change ((dualIso h R).hom.hom z).fst = (L.map (reduction R)).hom z
  rw [dualIso_fst]
  apply (r R).injective
  rw [h.2, (r R).apply_symm_apply]
  rfl

private theorem dualIso_constants (h : AlgebraCompatible e L r) (R : TestAlgebra K) :
    L.map (constants R) ≫ (dualIso h R).hom = constants (L.obj R) := by
  apply CommAlgCat.hom_ext
  apply AlgHom.ext
  intro z
  apply TrivSqZeroExt.ext
  · change ((dualIso h R).hom.hom ((L.map (constants R)).hom z)).fst = z
    rw [dualIso_fst, h.2]
    exact (r R).symm_apply_apply z
  · change ((dualIso h R).hom.hom ((L.map (constants R)).hom z)).snd = 0
    rw [dualIso_snd, h.2]
    exact map_zero (r R).symm

private theorem dualIso_scale (h : AlgebraCompatible e L r) (R : TestAlgebra K)
    (c : L.obj R) :
    L.map (scale R (r R c)) ≫ (dualIso h R).hom = (dualIso h R).hom ≫ scale (L.obj R) c := by
  apply CommAlgCat.hom_ext
  apply AlgHom.ext
  intro z
  apply TrivSqZeroExt.ext
  · change ((dualIso h R).hom.hom ((L.map (scale R (r R c))).hom z)).fst =
      ((dualIso h R).hom.hom z).fst
    rw [dualIso_fst, dualIso_fst, h.2]
    rfl
  · change ((dualIso h R).hom.hom ((L.map (scale R (r R c))).hom z)).snd =
      c * ((dualIso h R).hom.hom z).snd
    rw [dualIso_snd, dualIso_snd, h.2]
    change (r R).symm (r R c * (r (DA R) z).snd) = c * (r R).symm (r (DA R) z).snd
    rw [map_mul, (r R).symm_apply_apply]

private def pointIso {k : Type*} [Field k] (X : GroupScheme k) {A B : TestAlgebra k}
    (i : A ≅ B) : GroupPoints X A ≃* GroupPoints X B :=
  (((groupPointsFunctor k).obj X).mapIso i).groupIsoToMulEquiv

variable {X : GroupScheme F} {Y : GroupScheme K}

private def dualPoints (h : AlgebraCompatible e L r) (p : PointComparison L X Y) (R : TestAlgebra K) :
    GroupPoints Y (DA R) ≃* GroupPoints X (DA (L.obj R)) :=
  (p (DA R)).trans (pointIso X (dualIso h R))

private theorem dualPoints_square (h : AlgebraCompatible e L r) {p : PointComparison L X Y}
    (hp : IsNatural p) {R S : TestAlgebra K} {a : DA R ⟶ DA S} {b : DA (L.obj R) ⟶ DA (L.obj S)}
    (hab : L.map a ≫ (dualIso h S).hom = (dualIso h R).hom ≫ b) (v : GroupPoints Y (DA R)) :
    dualPoints h p S (mapPoints a v) = mapPoints b (dualPoints h p R v) := by
  change mapPoints (dualIso h S).hom (p (DA S) (mapPoints a v)) =
    mapPoints b (mapPoints (dualIso h R).hom (p (DA R) v))
  rw [hp, ← mapPoints_comp, ← mapPoints_comp, hab]

private theorem dualPoints_reduction (h : AlgebraCompatible e L r) {p : PointComparison L X Y}
    (hp : IsNatural p) (R : TestAlgebra K) (v : GroupPoints Y (DA R)) :
    mapPoints (reduction (L.obj R)) (dualPoints h p R v) = p R (mapPoints (reduction R) v) := by
  change mapPoints (reduction (L.obj R)) (mapPoints (dualIso h R).hom (p (DA R) v)) = _
  rw [← mapPoints_comp, dualIso_reduction h R, hp]

private theorem dualPoints_constants (h : AlgebraCompatible e L r) {p : PointComparison L X Y}
    (hp : IsNatural p) (R : TestAlgebra K) (v : GroupPoints Y R) :
    dualPoints h p R (mapPoints (constants R) v) = mapPoints (constants (L.obj R)) (p R v) := by
  change mapPoints (dualIso h R).hom (p (DA R) (mapPoints (constants R) v)) = _
  rw [hp, ← mapPoints_comp, dualIso_constants h R]

private def groundDualPoints (h : AlgebraCompatible e L r) (p : PointComparison L X Y) :
    GroupPoints Y (DA (CommAlgCat.of K K)) ≃* GroupPoints X (DA (CommAlgCat.of F F)) :=
  (dualPoints h p (CommAlgCat.of K K)).trans
    (pointIso X ((Functor.mapIso
      (F := { obj := DA
              map := @dualMap F _
              map_id := fun _ => CommAlgCat.hom_ext (AlgHom.ext fun _ =>
                TrivSqZeroExt.ext rfl rfl)
              map_comp := fun _ _ => CommAlgCat.hom_ext (AlgHom.ext fun _ =>
                TrivSqZeroExt.ext rfl rfl) } ) (baseIso h))))

private theorem groundDualPoints_apply (h : AlgebraCompatible e L r) (p : PointComparison L X Y)
    (v : GroupPoints Y (DA (CommAlgCat.of K K))) :
    groundDualPoints h p v =
      mapPoints (dualMap (baseIso h).hom) (dualPoints h p (CommAlgCat.of K K) v) := rfl

private theorem reduction_dualMap {k : Type*} [Field k] {A B : TestAlgebra k} (a : A ⟶ B) :
    dualMap a ≫ reduction B = reduction A ≫ a :=
  CommAlgCat.hom_ext (AlgHom.ext fun _ => rfl)

private theorem dualMap_comp {k : Type*} [Field k] {A B C : TestAlgebra k}
    (a : A ⟶ B) (b : B ⟶ C) :
    dualMap (a ≫ b) = dualMap a ≫ dualMap b :=
  CommAlgCat.hom_ext (AlgHom.ext fun _ => TrivSqZeroExt.ext rfl rfl)

private def lieCompare (h : AlgebraCompatible e L r) {p : PointComparison L X Y}
    (hp : IsNatural p) : Lie K Y ≃ Lie F X := by
  apply (groundDualPoints h p).toEquiv.subtypeEquiv
  intro x
  change mapPoints (dualReduction K) x = 1 ↔
    mapPoints (dualReduction F) (groundDualPoints h p x) = 1
  rw [groundDualPoints_apply, ← mapPoints_comp, reduction_dualMap, mapPoints_comp,
    dualPoints_reduction h hp]
  exact (((p (CommAlgCat.of K K)).trans (pointIso X (baseIso h))).map_eq_one_iff).symm

private theorem lieCompare_val (h : AlgebraCompatible e L r) {p : PointComparison L X Y}
    (hp : IsNatural p) (v : Lie K Y) :
    (lieCompare h hp v).toMul.val = groundDualPoints h p v.toMul.val := rfl

private theorem lieCompare_ne_zero (h : AlgebraCompatible e L r) {p : PointComparison L X Y}
    (hp : IsNatural p) (v : Lie K Y) : lieCompare h hp v ≠ 0 ↔ v ≠ 0 := by
  have hzero : lieCompare h hp 0 = 0 := Subtype.ext (map_one (groundDualPoints h p))
  rw [← hzero]
  exact (lieCompare h hp).injective.ne_iff

private theorem dualPoints_extend (h : AlgebraCompatible e L r) {p : PointComparison L X Y}
    (hp : IsNatural p) (R : TestAlgebra K) (v : Lie K Y) :
    dualPoints h p R (mapPoints (dualMap (CommAlgCat.ofHom (Algebra.ofId K R))) v.toMul.val) =
      mapPoints (dualMap (CommAlgCat.ofHom (Algebra.ofId F (L.obj R))))
        (lieCompare h hp v).toMul.val := by
  rw [dualPoints_square h hp (dualIso_dualMap h _), lieCompare_val, groundDualPoints_apply,
    ← mapPoints_comp, ← dualMap_comp]
  congr 2
  apply CommAlgCat.hom_ext
  apply AlgHom.ext
  intro x
  change (L.map (CommAlgCat.ofHom (Algebra.ofId K R))).hom x =
    algebraMap F (L.obj R) (e.symm (r (CommAlgCat.of K K) x))
  apply (r R).injective
  exact (h.2 (CommAlgCat.ofHom (Algebra.ofId K R)) x).trans (by
    rw [h.1, e.apply_symm_apply]
    rfl)

private theorem lieCompare_inclusion (h : AlgebraCompatible e L r) {p : PointComparison L X Y}
    (hp : IsNatural p) {A : GroupScheme F} {B : GroupScheme K}
    {i : A ⟶ X} {j : B ⟶ Y} {q : PointComparison L A B} (hq : IsNatural q)
    (hc : InclusionCompatible i j p q) (v : Lie K B) :
    lieCompare h hp (mapPointKernel j v) = mapPointKernel i (lieCompare h hq v) := by
  let R := DA (CommAlgCat.of K K)
  let θ := (dualIso h (CommAlgCat.of K K)).hom ≫ dualMap (baseIso h).hom
  have he : ∀ (U : GroupScheme F) (V : GroupScheme K) (s : PointComparison L U V)
      (x : GroupPoints V R),
      groundDualPoints h s x = mapPoints θ (s R x) := by
    intro U V s x
    exact (mapPoints_comp _ _ _).symm
  apply Subtype.ext
  change groundDualPoints h p (pointHom j R v.toMul.val) =
    pointHom i (DA (CommAlgCat.of F F)) (groundDualPoints h q v.toMul.val)
  rw [he, he, pointHom_natural]
  exact congrArg (mapPoints θ) (hc R v.toMul.val)

end DualNumbers

section Weights

private abbrev baseMap {k : Type*} [Field k] (R : TestAlgebra k) :
    CommAlgCat.of k k ⟶ R := CommAlgCat.ofHom (Algebra.ofId k R)

private def weightIdentity {k : Type*} [Field k] {G : GroupScheme k}
    (T : ClosedSubgroup G) (χ : Character T.group) (v : Lie k G)
    (R : TestAlgebra k) (x : GroupPoints T.group R) : Prop :=
  let p := mapPoints (dualMap (baseMap R)) v.toMul.val
  let g := mapPoints (constants R) (pointHom T.inclusion R x)
  g * p * g⁻¹ = mapPoints (scale R (characterValue χ R x)) p

private theorem weightIdentity_map {k : Type*} [Field k] {G : GroupScheme k}
    (T : ClosedSubgroup G) (χ : Character T.group) (v : Lie k G)
    {R S : TestAlgebra k} (a : R ⟶ S) (x : GroupPoints T.group R)
    (hv : weightIdentity T χ v R x) : weightIdentity T χ v S (mapPoints a x) := by
  have hbase : baseMap R ≫ a = baseMap S :=
    CommAlgCat.hom_ext (AlgHom.ext a.hom.commutes)
  have hconst : constants R ≫ dualMap a = a ≫ constants S :=
    CommAlgCat.hom_ext (AlgHom.ext fun _ => TrivSqZeroExt.ext rfl (map_zero a.hom))
  have hscale : scale R (characterValue χ R x) ≫ dualMap a =
      dualMap a ≫ scale S (characterValue χ S (mapPoints a x)) := by
    rw [characterValue_natural]
    apply CommAlgCat.hom_ext
    apply AlgHom.ext
    intro z
    apply TrivSqZeroExt.ext
    · rfl
    · exact map_mul a.hom _ _
  have he := congrArg (mapPoints (dualMap a)) hv
  change mapPoints (dualMap a) (_ * _ * _) = mapPoints (dualMap a) _ at he
  let f := (((groupPointsFunctor k).obj G).map (dualMap a)).hom
  change f (_ * _ * _) = f _ at he
  simp only [map_mul, map_inv] at he
  change
    mapPoints (dualMap a) (mapPoints (constants R) (pointHom T.inclusion R x)) *
      mapPoints (dualMap a) (mapPoints (dualMap (baseMap R)) v.toMul.val) *
      (mapPoints (dualMap a) (mapPoints (constants R) (pointHom T.inclusion R x)))⁻¹ =
    mapPoints (dualMap a) (mapPoints (scale R (characterValue χ R x))
      (mapPoints (dualMap (baseMap R)) v.toMul.val)) at he
  rw [← mapPoints_comp (constants R), hconst, mapPoints_comp,
    ← pointHom_natural, ← mapPoints_comp (dualMap (baseMap R)), ← dualMap_comp, hbase,
    ← mapPoints_comp (scale R _), hscale, mapPoints_comp,
    ← mapPoints_comp (dualMap (baseMap R)), ← dualMap_comp, hbase] at he
  exact he

variable (h : AlgebraCompatible e L r) (P : SplitBorelPair F) (Q : SplitBorelPair K)
variable [IsAffine P.T.group.X.left] [LocallyOfFiniteType P.T.group.X.hom]
variable [IsAffine Q.T.group.X.left]
variable {g : PointComparison L P.G.val Q.G.val} (hg : IsNatural g)
variable {t : PointComparison L P.T.group Q.T.group} (ht : IsNatural t)
variable (hT : InclusionCompatible P.T.inclusion Q.T.inclusion g t)

include hT in
private theorem weightIdentity_compare (χ : Character Q.T.group) (v : Lie K Q.G.val)
    (R : TestAlgebra K) (x : GroupPoints Q.T.group R) :
    weightIdentity Q.T χ v R x ↔
    weightIdentity P.T (characters h t ht χ) (lieCompare h hg v) (L.obj R) (t R x) := by
  let c := characterValue (characters h t ht χ) (L.obj R) (t R x)
  let y := pointHom Q.T.inclusion R x
  let a := mapPoints (constants R) y
  let p := mapPoints (dualMap (baseMap R)) v.toMul.val
  have hc : r R c = characterValue χ R x := characters_value h t ht χ R x
  have ha : dualPoints h g R a =
      mapPoints (constants (L.obj R)) (pointHom P.T.inclusion (L.obj R) (t R x)) := by
    rw [show a = mapPoints (constants R) y from rfl, dualPoints_constants h hg]
    exact congrArg (mapPoints (constants (L.obj R))) (hT R x)
  have hp := dualPoints_extend h hg R v
  change dualPoints h g R p = _ at hp
  have hs : dualPoints h g R (mapPoints (scale R (characterValue χ R x)) p) =
      mapPoints (scale (L.obj R) c) (dualPoints h g R p) := by
    rw [← hc]
    exact dualPoints_square h hg (dualIso_scale h R c) p
  change (a * p * a⁻¹ = mapPoints (scale R (characterValue χ R x)) p) ↔ _
  rw [← (dualPoints h g R).injective.eq_iff, map_mul, map_mul, map_inv, ha, hs, hp]
  rfl

include hT in
private theorem weightVectors_compare (χ : Character Q.T.group) (v : Lie K Q.G.val) :
    v ∈ adjointWeightVectors Q.T χ ↔
    lieCompare h hg v ∈ adjointWeightVectors P.T (characters h t ht χ) := by
  change (∀ R x, weightIdentity Q.T χ v R x) ↔
    ∀ R x, weightIdentity P.T (characters h t ht χ) (lieCompare h hg v) R x
  constructor
  · intro hv R x
    obtain ⟨S, ⟨z⟩⟩ := spectrumPresentation h P.T.group.X
    obtain ⟨f, rfl⟩ := point_factor z x
    obtain ⟨y, hy⟩ := (t S).surjective z.hom
    apply weightIdentity_map P.T _ _ f z.hom
    rw [← hy]
    exact (weightIdentity_compare h P Q hg ht hT χ v S y).mp (hv S y)
  · intro hv R x
    exact (weightIdentity_compare h P Q hg ht hT χ v R x).mpr (hv (L.obj R) (t R x))

include hg hT in
private theorem absoluteRoots_compare (χ : Character Q.T.group) :
    χ ∈ absoluteRoots Q.T ↔ characters h t ht χ ∈ absoluteRoots P.T := by
  have hne : χ ≠ 1 ↔ characters h t ht χ ≠ 1 := by
    rw [← (characters h t ht).map_one, (characters h t ht).injective.ne_iff]
  change (χ ≠ 1 ∧ _) ↔ (characters h t ht χ ≠ 1 ∧ _)
  rw [← hne]
  refine and_congr_right fun _ => ?_
  constructor
  · rintro ⟨v, hv, hn⟩
    exact ⟨lieCompare h hg v, (weightVectors_compare h P Q hg ht hT χ v).mp hv,
      (lieCompare_ne_zero h hg v).mpr hn⟩
  · rintro ⟨w, hw, hn⟩
    obtain ⟨v, rfl⟩ := (lieCompare h hg).surjective w
    exact ⟨v, (weightVectors_compare h P Q hg ht hT χ v).mpr hw,
      (lieCompare_ne_zero h hg v).mp hn⟩

private def roots : Root Q.T ≃ Root P.T :=
  (characters h t ht).toEquiv.subtypeEquiv (absoluteRoots_compare h P Q hg ht hT)

variable {b : PointComparison L P.B.group Q.B.group} (hb : IsNatural b)
variable (hB : InclusionCompatible P.B.inclusion Q.B.inclusion g b)

omit [IsAffine P.T.group.X.left] [LocallyOfFiniteType P.T.group.X.hom]
  [IsAffine Q.T.group.X.left] in
include hb hB in
private theorem lieImage_compare (v : Lie K Q.G.val) :
    v ∈ lieImage Q.B ↔ lieCompare h hg v ∈ lieImage P.B := by
  constructor
  · rintro ⟨w, hw⟩
    refine ⟨lieCompare h hb w, ?_⟩
    rw [← lieCompare_inclusion h hg hb hB, hw]
  · rintro ⟨w, hw⟩
    obtain ⟨z, rfl⟩ := (lieCompare h hb).surjective w
    refine ⟨z, (lieCompare h hg).injective ?_⟩
    rw [lieCompare_inclusion h hg hb hB, hw]

include hb hB in
private theorem subgroupRoots_compare (α : Root Q.T) :
    α ∈ subgroupRoots Q.T Q.B ↔
      roots h P Q hg ht hT α ∈ subgroupRoots P.T P.B := by
  change adjointWeightVectors Q.T α.val ⊆ lieImage Q.B ↔
    adjointWeightVectors P.T (characters h t ht α.val) ⊆ lieImage P.B
  constructor
  · intro hsub w hw
    obtain ⟨v, rfl⟩ := (lieCompare h hg).surjective w
    exact (lieImage_compare h P Q hg hb hB v).mp
      (hsub ((weightVectors_compare h P Q hg ht hT α.val v).mpr hw))
  · intro hsub v hv
    exact (lieImage_compare h P Q hg hb hB v).mpr
      (hsub ((weightVectors_compare h P Q hg ht hT α.val v).mp hv))

include hb hB in
private theorem simple_compare (α : Root Q.T) :
    IsSimple Q α ↔ IsSimple P (roots h P Q hg ht hT α) := by
  let a := roots h P Q hg ht hT
  let f := characters h t ht
  have ha (x : Root Q.T) : (a x).val = f x.val := rfl
  have hs := subgroupRoots_compare h P Q hg ht hT hb hB
  constructor
  · intro hα
    refine ⟨(hs α).mp hα.1, ?_⟩
    intro β hβ δ hδ he
    obtain ⟨β', rfl⟩ := a.surjective β
    obtain ⟨δ', rfl⟩ := a.surjective δ
    apply hα.2 β' ((hs β').mpr hβ) δ' ((hs δ').mpr hδ)
    apply f.injective
    rwa [map_mul, ← ha, ← ha, ← ha]
  · intro hα
    refine ⟨(hs α).mpr hα.1, ?_⟩
    intro β hβ δ hδ he
    apply hα.2 (a β) ((hs β).mp hβ) (a δ) ((hs δ).mp hδ)
    change (a α).val = (a β).val * (a δ).val
    rw [ha, ha, ha, ← map_mul, he]

end Weights

/-- The finite root set in the character lattice determines the Cartan entries. -/
private theorem pairing_eq_of_rootEquiv
    {I : Type u} {J : Type v} [Finite I]
    {X Y X' Y' : Type*}
    [AddCommGroup X] [AddCommGroup Y] [AddCommGroup X'] [AddCommGroup Y']
    [Module.IsTorsionFree ℤ X]
    (P : RootPairing I ℤ X Y) (Q : RootPairing J ℤ X' Y')
    (a : I ≃ J) (f : X ≃ₗ[ℤ] X') (h : ∀ i, f (P.root i) = Q.root (a i)) (i j : I) :
    P.pairing i j = Q.pairing (a i) (a j) := by
  let b := (Q.coroot' (a j)).comp f.toLinearMap
  have h₂ : b (P.root j) = 2 := by
    change Q.coroot' (a j) (f (P.root j)) = 2
    rw [h]
    exact Q.coroot_root_two (a j)
  have hr : Set.MapsTo (Module.preReflection (P.root j) b) (Set.range P.root) (Set.range P.root) := by
    rintro _ ⟨x, rfl⟩
    let y := a.symm (Q.reflectionPerm (a j) (a x))
    refine ⟨y, f.injective ?_⟩
    rw [h, show a y = Q.reflectionPerm (a j) (a x) from a.apply_symm_apply _,
      Q.root_reflectionPerm, Q.reflection_apply, Module.preReflection_apply, map_sub, map_smul, h, h]
    change _ = Q.root (a x) - Q.coroot' (a j) (f (P.root x)) • Q.root (a j)
    rw [h]
  have hpair := Module.Dual.eq_of_preReflection_mapsTo' (Set.finite_range P.root)
    (Submodule.subset_span (Set.mem_range_self j)) (P.coroot_root_two j)
    (P.mapsTo_reflection_root (i := j)) h₂ hr
  have h₀ := DFunLike.congr_fun hpair
    ⟨P.root i, Submodule.subset_span (Set.mem_range_self i)⟩
  change P.pairing i j = Q.coroot' (a j) (f (P.root i)) at h₀
  simpa only [h, RootPairing.root_coroot'_eq_pairing] using h₀

private theorem cartanType_of_rootEquiv
    {I : Type u} {J : Type v} [Finite I]
    {X Y X' Y' : Type*}
    [AddCommGroup X] [AddCommGroup Y] [AddCommGroup X'] [AddCommGroup Y']
    [Module.IsTorsionFree ℤ X]
    (P : RootPairing I ℤ X Y) (Q : RootPairing J ℤ X' Y')
    (B : P.Base) (C : Q.Base)
    (a : I ≃ J) (f : X ≃ₗ[ℤ] X') (h : ∀ i, f (P.root i) = Q.root (a i))
    (hs : ∀ i, i ∈ B.support ↔ a i ∈ C.support)
    (t : LieAlgebrasAndRepresentations.FiniteDynkinType)
    (ht : Specs.AbsoluteDynkinTypes.HasDynkinType (RootData.integralCartan P B) t) :
    Specs.AbsoluteDynkinTypes.HasDynkinType (RootData.integralCartan Q C) t := by
  let b : B.support ≃ C.support := a.subtypeEquiv hs
  obtain ⟨c, hc⟩ := ht
  refine ⟨b.symm.trans c, fun i j => ?_⟩
  have h₀ := pairing_eq_of_rootEquiv P Q a f h (b.symm j).val (b.symm i).val
  have hi : a (b.symm i).val = i.val := congrArg Subtype.val (b.apply_symm_apply i)
  have hj : a (b.symm j).val = j.val := congrArg Subtype.val (b.apply_symm_apply j)
  rw [hi, hj] at h₀
  exact h₀.symm.trans (hc (b.symm i) (b.symm j))

/-- Transport the F₄ Cartan type of an attached datum across the comparison. -/
theorem cartanType : Statement.{u} := by
  intro F _ K _ e L r h P Q g t b hg ht hb hT hB D E hd
  letI : IsAffine P.T.group.X.left := (Specs.Unipotent.closedSubgroupAlgebraicGroup P.T).prop.1
  letI : LocallyOfFiniteType P.T.group.X.hom :=
    (Specs.Unipotent.closedSubgroupAlgebraicGroup P.T).prop.2.1
  letI : IsAffine Q.T.group.X.left := (Specs.Unipotent.closedSubgroupAlgebraicGroup Q.T).prop.1
  letI := D.comm
  letI := E.comm
  letI := D.datum.finiteRoots
  letI := D.datum.freeCharacters
  let a := roots h P Q hg ht hT
  let f : Additive (Character Q.T.group) ≃ₗ[ℤ] Additive (Character P.T.group) :=
    (characters h t ht).toAdditive.toIntLinearEquiv
  have hroot (i : Root Q.T) : f (E.datum.rootDatum.root i) = D.datum.rootDatum.root (a i) := by
    rw [E.datum.root_eq, D.datum.root_eq]
    rfl
  have hroot' (i : Root P.T) : f.symm (D.datum.rootDatum.root i) = E.datum.rootDatum.root (a.symm i) := by
    apply f.injective
    rw [LinearEquiv.apply_symm_apply, hroot, Equiv.apply_symm_apply]
  have hsimple (i : Root P.T) : i ∈ D.base.support ↔ a.symm i ∈ E.base.support := by
    rw [D.simple_iff, E.simple_iff, simple_compare h P Q hg ht hT hb hB]
    change IsSimple P i ↔ IsSimple P (a (a.symm i))
    rw [Equiv.apply_symm_apply]
  exact cartanType_of_rootEquiv D.datum.rootDatum E.datum.rootDatum D.base E.base
    a.symm f.symm hroot' hsimple .F4 hd

end

end LinearAlgebraicGroups.Arithmetic.F4RealCompletionCartan
