import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Arithmetic.ExceptionalInnerWeylDirections
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.ExceptionalInnerStandardTorusDescent
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.AffineArrangementAlcoves
import Batteries.Tactic.OpenPrivate

open AlgebraicGeometry CategoryTheory CategoryTheory.MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj TensorProduct

universe u

namespace LinearAlgebraicGroups.Arithmetic.ExceptionalInnerWeylDirections

open LinearAlgebraicGroups.Specs
open Specs.ExceptionalAffineRootSystems (ApartmentRoots exceptionalCartan simpleRootValues)
open Specs.ExceptionalAffineBruhat (ExceptionalNumbering FieldPoints SplitLevel)
open Specs.ExceptionalInnerWeylDirections (MarkedWeylDirections reflectValues reflectWord)
open Specs.ExceptionalIwahoriImageComparison (MarkedCentralCover markedGroundPoint)
open Specs.ExceptionalInnerStandardTorusDescent (markedCocharacterMap)
open Specs.CharacterDescent (Cocharacter)
open Specs.IntegralSemisimpleModel (Model)
open Specs.Pinning (BasedRootDatum)

open private cover_simple markedGroundEquiv markedGroundEquiv_apply
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.ExceptionalIwahoriImageComparison
open private latticeCharacter latticeCharacterPairing markedCocharacterMap_apply markedNormalizerCharacter
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.ExceptionalInnerStandardTorusDescent
open private conjugationIso conjugation comp_conjugation
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Descent.FiniteFieldFlags

noncomputable section

private theorem centralRootValue {D E : BasedRootDatum.{u}} {M : Model D} {M' : Model E}
    (c : MarkedCentralCover M M') (i : D.I) (x : ℚ ⊗[ℤ] D.Y) :
    (ApartmentRoots.split E.datum ℚ).root (c.rootEquiv i) (c.pushCocharacter.baseChange ℚ x) =
      (ApartmentRoots.split D.datum ℚ).root i x := by
  have h : (E.datum.root' (c.rootEquiv i)).comp c.pushCocharacter = D.datum.root' i := by
    ext y
    change E.datum.toLinearMap (E.datum.root (c.rootEquiv i)) (c.pushCocharacter y) =
      D.datum.toLinearMap (D.datum.root i) y
    rw [← c.pairing, c.roots]
  change ((RootData.extendFunctional ℚ (E.datum.root' (c.rootEquiv i))).comp
    (c.pushCocharacter.baseChange ℚ)) x = RootData.extendFunctional ℚ (D.datum.root' i) x
  rw [RootData.extendFunctional, LinearMap.comp_assoc, ← LinearMap.baseChange_comp, h]
  rfl

private theorem exceptionalCartan_comm (n : ℕ) (i j : Fin n) :
    exceptionalCartan n i j = exceptionalCartan n j i := by
  by_cases h : i = j
  · subst j
    rfl
  · simp only [exceptionalCartan, ite_eq_right h, ite_eq_right (Ne.symm h)]
    rw [Finset.pair_comm i.val j.val]

private theorem simpleRootValues_reflection {D : BasedRootDatum.{u}} {n : ℕ}
    (b : Fin n ≃ D.base.support) (hb : ExceptionalNumbering D n b)
    (j : Fin n) (x : ℚ ⊗[ℤ] D.Y) :
    simpleRootValues D.datum D.base b ℚ ((ApartmentRoots.split D.datum ℚ).linearReflection (b j) x) =
      reflectValues j (simpleRootValues D.datum D.base b ℚ x) := by
  let A := ApartmentRoots.split D.datum ℚ
  funext i
  change A.root (b i) (x - A.root (b j) x • A.coroot (b j)) =
    A.root (b i) x - (exceptionalCartan n j i : ℚ) * A.root (b j) x
  have hpair : A.root (b i) (A.coroot (b j)) = (exceptionalCartan n j i : ℚ) := by
    change RootData.extendFunctional ℚ (D.datum.root' (b i)) (1 ⊗ₜ[ℤ] D.datum.coroot (b j)) = _
    rw [RootData.extendFunctional_one_tmul]
    change (D.datum.pairing (b i) (b j) : ℚ) = _
    rw [hb.2, exceptionalCartan_comm n i j]
  rw [map_sub, map_smul, hpair, smul_eq_mul, mul_comm (A.root (b j) x)]

private theorem simpleRootValues_reflectionWord {D : BasedRootDatum.{u}} {n : ℕ}
    (b : Fin n ≃ D.base.support) (hb : ExceptionalNumbering D n b)
    (word : List (Fin n)) (x : ℚ ⊗[ℤ] D.Y) :
    simpleRootValues D.datum D.base b ℚ
      (word.foldl (fun z j => (ApartmentRoots.split D.datum ℚ).linearReflection (b j) z) x) =
      reflectWord word (simpleRootValues D.datum D.base b ℚ x) := by
  induction word generalizing x with
  | nil => rfl
  | cons j js ih =>
    rw [List.foldl_cons, ih, simpleRootValues_reflection b hb]
    rfl

private def affineReflectionWord {D : BasedRootDatum.{u}} {n : ℕ}
    (b : Fin n ≃ D.base.support) : List (Fin n) → (ApartmentRoots.split D.datum ℚ).affineWeylGroup
  | [] => 1
  | j :: js => affineReflectionWord b js *
      ⟨(ApartmentRoots.split D.datum ℚ).reflection (b j, 0),
        Subgroup.subset_closure ⟨(b j, 0), rfl⟩⟩

private theorem affineReflectionWord_linear {D : BasedRootDatum.{u}} {n : ℕ}
    (b : Fin n ≃ D.base.support) (word : List (Fin n)) (x : ℚ ⊗[ℤ] D.Y) :
    (affineReflectionWord b word).val.linear x =
      word.foldl (fun z j => (ApartmentRoots.split D.datum ℚ).linearReflection (b j) z) x := by
  induction word generalizing x with
  | nil => rfl
  | cons j js ih =>
    change (affineReflectionWord b js).val.linear
      (((ApartmentRoots.split D.datum ℚ).reflection (b j, 0)).linear x) = _
    rw [AffineArrangement.reflection_linear, ih]
    rfl

private theorem affineReflectionWord_apply {D : BasedRootDatum.{u}} {n : ℕ}
    (b : Fin n ≃ D.base.support) (word : List (Fin n)) (x : ℚ ⊗[ℤ] D.Y) :
    (affineReflectionWord b word).val x =
      word.foldl (fun z j => (ApartmentRoots.split D.datum ℚ).wallReflection (b j) 0 z) x := by
  induction word generalizing x with
  | nil => rfl
  | cons j js ih =>
    change (affineReflectionWord b js).val
      ((ApartmentRoots.split D.datum ℚ).wallReflection (b j) 0 x) = _
    exact ih _

section SplitLevel

variable {K : Type u} [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    {D E : BasedRootDatum.{u}} {M : Model D} {M' : Model E}
    {c : MarkedCentralCover M M'} {p : ℚ ⊗[ℤ] D.Y} {p' : ℚ ⊗[ℤ] E.Y}
    {e : (ℚ ⊗[ℤ] D.Y) ≃ₗ[ℚ] (ℚ ⊗[ℤ] E.Y)}
    {Y : SplitLevel K c p p' e}

set_option backward.isDefEq.respectTransparency false in
private theorem markedConjugatedCocharacterMap (v : Y.sc.N)
    (g : 𝟙_ (SchemeOver K) ⟶ Y.sc_fibre.realization.pinned.pair.G.val.X)
    (hg : markedGroundPoint Y.sc_fibre g = (v : FieldPoints M K))
    (a : Y.sc_fibre.realization.pinned.pair.T.group ≅ Y.sc_fibre.realization.pinned.pair.T.group)
    (ha : let P := Y.sc_fibre.realization.pinned.pair
      (a.hom ≫ P.T.inclusion).hom.hom =
        (toUnit P.T.group.X ≫ g) * P.T.inclusion.hom.hom * (toUnit P.T.group.X ≫ g)⁻¹)
    {H : GroupScheme K} [IsCommMonObj H.X]
    (s : H ⟶ Y.sc_fibre.realization.pinned.pair.T.group) :
    (markedCocharacterMap Y.sc_fibre (s ≫ a.hom)).baseChange ℚ =
      (Y.sc.affine v).linear.toLinearMap.comp ((markedCocharacterMap Y.sc_fibre s).baseChange ℚ) := by
  let C := Y.sc_fibre
  let P := C.realization.pinned.pair
  let _ := C.realization.attached.comm
  let d := C.realization.datumIso.val.coweightEquiv
  have hconj : a.hom ≫ P.T.inclusion = P.T.inclusion ≫ (conjugationIso g).hom := by
    apply Grp.hom_ext
    change (a.hom ≫ P.T.inclusion).hom.hom = P.T.inclusion.hom.hom ≫ conjugation g
    rw [comp_conjugation]
    exact ha
  obtain ⟨N, hN, _⟩ := Y.sc_points.2.1.2
  let _ := N.torusComm
  obtain ⟨m, hm, hl⟩ := hN v
  change N.point m = (v : FieldPoints M K) at hm
  change N.label m = Y.sc.localIwahori.normalizer.label v at hl
  let w := (N.label m).val
  have hlin : (Y.sc.affine v).linear = w.coweightEquiv.symm.baseChange ℤ ℚ D.Y D.Y := by
    apply LinearEquiv.ext
    intro x
    have h z := Y.sc_points.2.2.2.2.2.2.1 v z
    rw [← hl] at h
    have hmap := (Y.sc.affine v).map_vadd (0 : ℚ ⊗[ℤ] D.Y) x
    rw [vadd_eq_add, add_zero, vadd_eq_add, h x, h 0, LinearEquiv.map_zero, zero_add] at hmap
    exact (add_left_inj _).mp hmap.symm
  have hc (y : Cocharacter P.T.group) :
      d (Additive.ofMul (y ≫ a.hom)) = w.coweightEquiv.symm (d (Additive.ofMul y)) := by
    apply D.datum.toLinearMap.flip.toPerfPair.injective
    ext x
    have hdual := w.toLinearMap_weightEquiv (w.weightEquiv.symm x)
      (w.coweightEquiv.symm (d (Additive.ofMul y)))
    rw [w.weightEquiv.apply_symm_apply, w.coweightEquiv.apply_symm_apply] at hdual
    change D.datum.toLinearMap x (d (Additive.ofMul (y ≫ a.hom))) =
      D.datum.toLinearMap x (w.coweightEquiv.symm (d (Additive.ofMul y)))
    rw [hdual, latticeCharacterPairing, latticeCharacterPairing]
    have hχ := markedNormalizerCharacter C N g a hconj m (hg.trans hm.symm) x
    exact congrArg (Function.invFun (Specs.CharacterPairing.powerMorphism (k := K)))
      ((Category.assoc y a.hom (latticeCharacter C x)).trans (congrArg (y ≫ ·) hχ))
  have hmap : markedCocharacterMap C (s ≫ a.hom) =
      w.coweightEquiv.symm.toLinearMap.comp (markedCocharacterMap C s) := by
    ext y
    change markedCocharacterMap C (s ≫ a.hom) (Additive.ofMul y.toMul) =
      w.coweightEquiv.symm (markedCocharacterMap C s (Additive.ofMul y.toMul))
    rw [markedCocharacterMap_apply, markedCocharacterMap_apply, ← Category.assoc]
    exact hc (y.toMul ≫ s)
  change (markedCocharacterMap C (s ≫ a.hom)).baseChange ℚ = _
  rw [hmap, hlin, LinearMap.baseChange_comp]
  rfl

end SplitLevel

/-- A marked normalizer lift of a simple reflection word transports the
cocharacter image by that word in the common simple-root coordinates. -/
theorem markedWeylDirections : MarkedWeylDirections.{u} := by
  intro K _ _ _ _ D E M M' c p p' e Y n b _ hb hrank word
  let bAd := b.trans (c.rootEquiv.subtypeEquiv (cover_simple c))
  have hAd : ExceptionalNumbering E n bAd := by
    refine ⟨hrank, fun i j => ?_⟩
    change E.datum.pairing (c.rootEquiv (b i)) (c.rootEquiv (b j)) = _
    have h := c.pairing (E.datum.root (c.rootEquiv (b i))) (D.datum.coroot (b j))
    rw [c.roots, c.coroots] at h
    exact h.symm.trans (hb.2 i j)
  let values := simpleRootValues D.datum D.base b ℚ
  let valuesAd := simpleRootValues E.datum E.base bAd ℚ
  have hcentral (x : ℚ ⊗[ℤ] D.Y) : valuesAd (c.pushCocharacter.baseChange ℚ x) = values x := by
    funext i
    exact centralRootValue c (b i) x
  let w := affineReflectionWord b word
  let v := Y.sc.lift w
  let g := (markedGroundEquiv Y.sc_fibre).symm (v : FieldPoints M K)
  have hg : markedGroundPoint Y.sc_fibre g = (v : FieldPoints M K) :=
    (markedGroundEquiv_apply Y.sc_fibre g).symm.trans
      ((markedGroundEquiv Y.sc_fibre).apply_symm_apply _)
  have hmem : markedGroundPoint Y.sc_fibre g ∈ Y.sc.N := hg.symm ▸ v.property
  have hv : (⟨markedGroundPoint Y.sc_fibre g, hmem⟩ : Y.sc.N) = v := Subtype.ext hg
  refine ⟨bAd, hAd, fun _ => rfl, hcentral, g, hmem, ?_, ?_⟩
  · rw [hv, Y.sc.lift_label w]
    exact affineReflectionWord_apply b word
  · intro a ha H _ s
    have hconj := markedConjugatedCocharacterMap (Y := Y) v g hg a ha s
    simp only [LinearMap.coe_range, ← Set.range_comp, Function.comp_def, LinearMap.comp_apply]
    congr 1
    funext x
    rw [hconj, LinearMap.comp_apply, Y.sc.lift_label w]
    let z := (markedCocharacterMap Y.sc_fibre s).baseChange ℚ x
    change values ((affineReflectionWord b word).val.linear z) =
      reflectWord word (valuesAd (c.pushCocharacter.baseChange ℚ z))
    rw [affineReflectionWord_linear b word z, hcentral z]
    exact simpleRootValues_reflectionWord b hb word z

end

end LinearAlgebraicGroups.Arithmetic.ExceptionalInnerWeylDirections
