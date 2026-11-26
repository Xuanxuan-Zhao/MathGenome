import Specs.LinearAlgebraicGroups.Arithmetic.LocalMixingRootMarkNormalization
import LinearAlgebraicGroups.Arithmetic.TrialitarianRelativeRoots
import Batteries.Tactic.OpenPrivate

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj Matrix

universe u

namespace LinearAlgebraicGroups.Arithmetic.LocalMixingRootMarkNormalization

open LinearAlgebraicGroups.Specs
open Specs.Arithmetic.LocalMixingRootMarkNormalization (RootMarkNormalization)
open CharacterDescent (Character Cocharacter)
open CharacterPairing (absoluteRoots characterValue)
open Specs.GeometricRadicals (IsReductive IsSplitTorus baseChangedSubgroup)
open Specs.RankOneFlag (IsGeometricallyMaximal)
open Specs.Unipotent (baseChangedAlgebraicGroup)
open Specs.QuasiSplitOrbitLevis (MultiplicativeComparison PreservesUnits)
open Specs.RootGroups (AdditiveLine HasScalarAction IsRootSubgroup rootPoint)
open Specs.AdjointRepresentation (GroupPoints)
open Specs.IntegralFibreReductivity (rankOnePoints)
open Specs.IntegralRootRelations (upper lower diagonal)
open CocharacterDynamics (cocharacterPoint)

open private same_subgroup_trans from LinearAlgebraicGroups.RootData.RankOneFlag
open private rootPoint_surjective from LinearAlgebraicGroups.RootData.OrderedRootProducts
open private rootPoint_comp normalizes_of_point_conjugation tangent_weight_of_scalarAction
  rootPoint_injective_of_mono rootPoint_natural from LinearAlgebraicGroups.RootData.RootGroups
open private scalarCharacter scalarCharacter_comparison scalarCharacterEquiv
  scalarMorphism scalarMorphism_baseChange scalarMorphism_descends
  from LinearAlgebraicGroups.Arithmetic.QuasiSplitFixedWeyl
open private unitComparison_unique from LinearAlgebraicGroups.Arithmetic.TrialitarianRelativeRoots
open private multiplicativeBaseChange multiplicativeBaseChange_unit
  from LinearAlgebraicGroups.Relative.RationalCocharacter
open private mono_over from LinearAlgebraicGroups.Affine.Stabilizers
open private isIso_of_scalarExtension from LinearAlgebraicGroups.Classification.SimplyConnectedLattice
open private baseChangeMapPullback from LinearAlgebraicGroups.Affine.Components
open LinearAlgebraicGroups.RootData.OrderedRootProducts
open LinearAlgebraicGroups.RootData.RootGroups
open LinearAlgebraicGroups (baseChangeClosedSubgroup)

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
set_option linter.style.haveILetI false

variable {F : Type u} [Field F]

/- An isomorphism over the ground field preserves the structure morphism. -/
private theorem smooth_additiveLine (A : AdditiveLine F) : Smooth A.group.X.hom := by
  change Smooth (Spec.map (CommRingCat.ofHom (algebraMap F (Polynomial F))))
  rw [HasRingHomProperty.Spec_iff (P := @Smooth)]
  change (algebraMap F (Polynomial F)).Smooth
  exact RingHom.smooth_algebraMap.mpr ⟨inferInstance, inferInstance⟩

private theorem isRootSubgroup_of_scalarAction {X : GroupScheme F} (S U : ClosedSubgroup X)
    (a : Character S.group) (A : AdditiveLine F) (x : A.group ≅ U.group)
    (hx : HasScalarAction S a (x.hom ≫ U.inclusion)) : IsRootSubgroup S U a := by
  have hleft : IsIso x.hom.hom.hom.left :=
    ((Grp.forget (SchemeOver F)) ⋙ Over.forget _).map_isIso x.hom
  refine ⟨?_, ⟨A.operations, A.comultiplication, A.counit, A.antipode, ⟨x.symm⟩⟩, ?_,
    tangent_weight_of_scalarAction S U a A x hx⟩
  · exact (MorphismProperty.cancel_left_of_respectsIso @Smooth x.hom.hom.hom.left _).mp
      ((Over.w x.hom.hom.hom).symm ▸ smooth_additiveLine A)
  · apply normalizes_of_point_conjugation S U
    intro R t p
    obtain ⟨b, rfl⟩ := rootPoint_surjective x R p
    refine ⟨rootPoint x.hom R (characterValue a R t * b), ?_⟩
    rw [← rootPoint_comp, ← rootPoint_comp]
    exact (hx R t b).symm

private theorem closedImmersion_of_baseChange {K : Type u} [Field K] [Algebra F K]
    (H G : AffineAlgebraicGroup F) (f : H.val ⟶ G.val)
    (hf : IsClosedImmersion ((groupBaseChange F K).map f).hom.hom.left) :
    IsClosedImmersion f.hom.hom.left := by
  let E := groupBaseChange F K
  obtain ⟨I, p, j, ⟨hpj, hflat, hsurj, _, _, hj⟩, _, _⟩ := schemeImageFactorization H G f
  have hflat' : Flat (E.map p).hom.hom.left :=
    MorphismProperty.of_isPullback (baseChangeMapPullback (K := K) p.hom.hom).flip hflat
  have hsurj' : Surjective (E.map p).hom.hom.left :=
    MorphismProperty.of_isPullback (baseChangeMapPullback (K := K) p.hom.hom).flip hsurj
  have hj' := baseChangeClosedSubgroup F K j hj
  have hpj' : E.map p ≫ E.map j = E.map f := (E.map_comp _ _).symm.trans (E.congr_map hpj)
  obtain ⟨e, he, _⟩ := schemeImageUniqueness
    (baseChangedAlgebraicGroup K H) (baseChangedAlgebraicGroup K G) (E.map f)
    (E.map p) (E.map j) (𝟙 _) (E.map f) hpj' (Category.id_comp _)
    hflat' hsurj' hj' (inferInstanceAs (Flat (𝟙 (E.obj H.val).X.left)))
    (inferInstanceAs (Surjective (𝟙 (E.obj H.val).X.left))) hf
  haveI : IsIso (E.map p ≫ e.hom) := he.1.symm ▸ inferInstanceAs (IsIso (𝟙 (E.obj H.val)))
  haveI : IsIso (E.map p) := IsIso.of_isIso_comp_right (E.map p) e.hom
  haveI : IsIso p := isIso_of_scalarExtension K p inferInstance
  haveI : IsIso p.hom.hom.left :=
    (Grp.forget (SchemeOver F) ⋙ Over.forget _).map_isIso p
  rw [← hpj]
  exact IsClosedImmersion.comp p.hom.hom.left j.hom.hom.left

private theorem descend_closedEmbedding
    {K : Type u} [Field K] [Algebra F K] [IsGalois F K] (H G : AffineAlgebraicGroup F)
    (f : (groupBaseChange F K).obj H.val ⟶ (groupBaseChange F K).obj G.val)
    (hf : IsClosedImmersion f.hom.hom.left) (hfix : ∀ σ : Gal(K/F), scalarMorphism σ f = f) :
    ∃ g : H.val ⟶ G.val,
      (groupBaseChange F K).map g = f ∧ IsClosedImmersion g.hom.hom.left := by
  obtain ⟨g, hg⟩ := scalarMorphism_descends H G f hfix
  exact ⟨g, hg, closedImmersion_of_baseChange H G g (hg.symm ▸ hf)⟩

open Specs.Arithmetic.QuasiSplitFixedWeyl (scalarTransport)
open private SemilinearTestMap SemilinearTestMap.restrict semilinearSource semilinearSourceMap semilinearFieldMap
  semilinearPoint semilinearPoint_apply semilinearPoint_natural semilinearPoint_bijective
  scalarMorphism_left scalarTransport_cancel scalarCharacter_value
  from LinearAlgebraicGroups.Arithmetic.QuasiSplitFixedWeyl
open private additiveBaseChange from LinearAlgebraicGroups.Arithmetic.TrialitarianPinnedBorelPair
open private sameSubgroupIso from LinearAlgebraicGroups.Classification.CentralIsogenies
open private additiveIso_linear scaleIso scaleIso_point
  from LinearAlgebraicGroups.Classification.Pinning
open private rootPoint_eq additiveLineGroup hom_ext_on_affine_tests
  from LinearAlgebraicGroups.RootData.RootGroups

variable {K : Type u} [Field K] [Algebra F K]

private theorem scalarMorphism_closed (σ : Gal(K/F)) {A B : GroupScheme F}
    (x : (groupBaseChange F K).obj A ⟶ (groupBaseChange F K).obj B)
    (hx : IsClosedImmersion x.hom.hom.left) :
    IsClosedImmersion (scalarMorphism σ x).hom.hom.left := by
  have iso (τ : Gal(K/F)) (Q : GroupScheme F) : IsIso (scalarTransport τ Q.X) :=
    ⟨⟨scalarTransport τ⁻¹ Q.X,
      by simpa only [inv_inv] using scalarTransport_cancel τ⁻¹ Q,
      scalarTransport_cancel τ Q⟩⟩
  letI := iso σ A
  letI := iso σ⁻¹ B
  rw [scalarMorphism_left]
  infer_instance

private theorem semilinear_additiveMark {A₀ : AdditiveLine F} {A : AdditiveLine K}
    (e : (groupBaseChange F K).obj A₀.group ≅ A.group)
    (he : ∀ (R : TestAlgebra K) (v : R),
      baseChangePoint F K A₀.group.X R (rootPoint e.inv R v) =
        rootPoint (𝟙 A₀.group) ((restrictTestAlgebra F K).obj R) v)
    {σ : Gal(K/F)} {R U : TestAlgebra K} (a : SemilinearTestMap σ R U) (v : R) :
    semilinearPoint A₀.group a (rootPoint e.inv R v) = rootPoint e.inv U ((SemilinearTestMap.restrict a).hom v) := by
  apply (baseChangePoints F K A₀.group.X U).injective
  rw [semilinearPoint_apply, he, he]
  exact rootPoint_natural (𝟙 A₀.group) (SemilinearTestMap.restrict a) v

private theorem semilinear_rootMark {B : GroupScheme F}
    {A₀ : AdditiveLine F} {A : AdditiveLine K}
    (e : (groupBaseChange F K).obj A₀.group ≅ A.group)
    (he : ∀ (R : TestAlgebra K) (v : R),
      baseChangePoint F K A₀.group.X R (rootPoint e.inv R v) =
        rootPoint (𝟙 A₀.group) ((restrictTestAlgebra F K).obj R) v)
    (x : A.group ⟶ (groupBaseChange F K).obj B)
    {σ : Gal(K/F)} {R U : TestAlgebra K} (a : SemilinearTestMap σ R U) (v : R) :
    semilinearPoint B a (rootPoint x R v) =
      rootPoint (e.inv ≫ scalarMorphism σ (e.hom ≫ x)) U ((SemilinearTestMap.restrict a).hom v) := by
  rw [rootPoint_comp, ← semilinear_additiveMark e he a v, ← semilinearPoint_natural]
  rw [← rootPoint_comp, Iso.inv_hom_id_assoc]

/-- Fixed absolute roots have semilinear actions on their parameters by scalars. -/
private theorem fixedRoot_scales {G : AffineAlgebraicGroup F} {T : ClosedSubgroup G.val}
    (hT : IsClosedImmersion ((groupBaseChange F K).map T.inclusion).hom.hom.left)
    (hG : IsReductive (baseChangedAlgebraicGroup K G))
    (hs : IsSplitTorus ((groupBaseChange F K).obj T.group))
    (hm : IsGeometricallyMaximal (baseChangedSubgroup K T hT))
    (χ : Character ((groupBaseChange F K).obj T.group))
    (hχ : χ ∈ absoluteRoots (baseChangedSubgroup K T hT))
    {A₀ : AdditiveLine F} {A : AdditiveLine K}
    (e : (groupBaseChange F K).obj A₀.group ≅ A.group)
    (he : ∀ (R : TestAlgebra K) (v : R),
      baseChangePoint F K A₀.group.X R (rootPoint e.inv R v) =
        rootPoint (𝟙 A₀.group) ((restrictTestAlgebra F K).obj R) v)
    (x : A.group ⟶ (groupBaseChange F K).obj G.val) (hx : IsClosedImmersion x.hom.hom.left)
    (ha : HasScalarAction (baseChangedSubgroup K T hT) χ x) (σ : Gal(K/F))
    (hfix : scalarCharacter σ χ = χ) :
    ∃ d : Kˣ, ∀ {R U : TestAlgebra K} (a : SemilinearTestMap σ R U) (v : R),
      semilinearPoint G.val a (rootPoint x R v) =
        rootPoint x U (algebraMap K U (d : K) * (SemilinearTestMap.restrict a).hom v) := by
  let E := groupBaseChange F K
  let GK := baseChangedAlgebraicGroup K G
  let TK := baseChangedSubgroup K T hT
  let y := e.inv ≫ scalarMorphism σ (e.hom ≫ x)
  haveI : IsIso e.hom.hom.hom.left :=
    (Grp.forget (SchemeOver K) ⋙ Over.forget _).map_isIso e.hom
  haveI : IsIso e.inv.hom.hom.left :=
    (Grp.forget (SchemeOver K) ⋙ Over.forget _).map_isIso e.inv
  haveI : IsClosedImmersion x.hom.hom.left := hx
  haveI : IsClosedImmersion (scalarMorphism σ (e.hom ≫ x)).hom.hom.left :=
    scalarMorphism_closed σ _ (IsClosedImmersion.comp e.hom.hom.hom.left x.hom.hom.left)
  have hy : IsClosedImmersion y.hom.hom.left := IsClosedImmersion.comp _ _
  have ht : HasScalarAction TK χ y := by
    intro U t z
    let R := semilinearSource σ U
    let a := semilinearSourceMap σ U
    obtain ⟨p, hp⟩ := (semilinearPoint_bijective T.group a Function.bijective_id).surjective t
    let w : R := z
    let p' : GroupPoints (E.obj G.val) R := p ≫ (E.map T.inclusion).hom.hom
    have h := congrArg (semilinearPoint G.val a) (ha R p w)
    change semilinearPoint G.val a
      (p' * rootPoint x R w * p'⁻¹) =
      semilinearPoint G.val a (rootPoint x R (characterValue χ R p * w)) at h
    dsimp only [p'] at h
    have hinc : scalarMorphism σ (E.map T.inclusion) = E.map T.inclusion :=
      scalarMorphism_baseChange σ T.inclusion
    rw [map_mul, map_mul, map_inv, semilinearPoint_natural σ a (E.map T.inclusion),
      hinc, hp, semilinear_rootMark e he x a w,
      semilinear_rootMark e he x a (characterValue χ R p * w)] at h
    have hv := scalarCharacter_value a χ p
    change characterValue (scalarCharacter σ χ) U (semilinearPoint T.group a p) =
      (SemilinearTestMap.restrict a).hom (characterValue χ R p) at hv
    rw [hfix, hp] at hv
    rw [map_mul, ← hv, show (SemilinearTestMap.restrict a).hom w = z from rfl] at h
    exact h
  let U : ClosedSubgroup GK.val := ⟨A.group, x, hx⟩
  let V : ClosedSubgroup GK.val := ⟨A.group, y, hy⟩
  obtain ⟨W, _, _, _, _, hW⟩ := (RootData.RootGroups.rootSubgroups GK hG TK hs hm).2 χ hχ |>.2.2
  have hU := isRootSubgroup_of_scalarAction TK U χ A (Iso.refl _) (by
    change HasScalarAction TK χ (𝟙 A.group ≫ x)
    rwa [Category.id_comp])
  have hV := isRootSubgroup_of_scalarAction TK V χ A (Iso.refl _) (by
    change HasScalarAction TK χ (𝟙 A.group ≫ y)
    rwa [Category.id_comp])
  obtain ⟨s, hs'⟩ := sameSubgroupIso (same_subgroup_trans
    (A := V) (B := W) (C := U) (hW V hV).symm (hW U hU))
  change A.group ≅ A.group at s
  change s.hom ≫ x = y at hs'
  obtain ⟨d, hd⟩ := additiveIso_linear A A s
  refine ⟨d, fun {R U} a v => (semilinear_rootMark e he x a v).trans ?_⟩
  rw [show e.inv ≫ scalarMorphism σ (e.hom ≫ x) = s.hom ≫ x from hs'.symm,
    rootPoint_comp, hd, rootPoint_eq]

open private mapPoints_comp from LinearAlgebraicGroups.RootData.CharacterPairing
private theorem semilinearFieldPoint_mul (B : GroupScheme F) (σ τ : Gal(K/F))
    (p : GroupPoints ((groupBaseChange F K).obj B) (CommAlgCat.of K K)) :
    semilinearPoint B (semilinearFieldMap (σ * τ)) p =
      semilinearPoint B (semilinearFieldMap σ) (semilinearPoint B (semilinearFieldMap τ) p) := by
  apply (baseChangePoints F K B.X (CommAlgCat.of K K)).injective
  rw [semilinearPoint_apply, semilinearPoint_apply, semilinearPoint_apply, ← mapPoints_comp]
  congr 1

private theorem rootMark_scalarCocycle {B : GroupScheme F} {A : AdditiveLine K}
    (x : A.group ⟶ (groupBaseChange F K).obj B) (hx : IsClosedImmersion x.hom.hom.left)
    (d : Gal(K/F) → Kˣ)
    (hd : ∀ (σ : Gal(K/F)) {R U : TestAlgebra K} (a : SemilinearTestMap σ R U) (v : R),
      semilinearPoint B a (rootPoint x R v) =
        rootPoint x U (algebraMap K U (d σ : K) * (SemilinearTestMap.restrict a).hom v)) :
    ∀ σ τ, d (σ * τ) = d σ * Units.map σ.toRingHom.toMonoidHom (d τ) := by
  intro σ τ
  let R := CommAlgCat.of K K
  have h := semilinearFieldPoint_mul B σ τ (rootPoint x R 1)
  rw [hd, hd τ, hd σ] at h
  haveI : Mono x.hom.hom := mono_over _ hx
  apply Units.ext
  have hz := rootPoint_injective_of_mono x R h
  change (d (σ * τ) : K) * (σ * τ) (1 : K) =
    (d σ : K) * σ ((d τ : K) * τ (1 : K)) at hz
  change (d (σ * τ) : K) = (d σ : K) * σ (d τ : K)
  simpa only [map_one, mul_one] using hz

/-- Scalar Hilbert 90 in the normalization used by the upper root mark. -/
private theorem fixedScalar [FiniteDimensional F K] [IsGalois F K] (d : Gal(K/F) → Kˣ)
    (hd : ∀ σ τ, d (σ * τ) = d σ * Units.map σ.toRingHom.toMonoidHom (d τ)) :
    ∃ v : Kˣ, ∀ σ, d σ * Units.map σ.toRingHom.toMonoidHom v = v := by
  let f (σ : Gal(K/F)) (z : K) : K := (d σ : K) * σ z
  have h1 : d 1 = 1 := by
    have h := hd 1 1
    change d (1 * 1) = d 1 * d 1 at h
    rw [one_mul] at h
    exact mul_left_cancel (h.symm.trans (mul_one _).symm)
  have hone (z : K) : f 1 z = z := by simp [f, h1]
  have hmul (σ τ : Gal(K/F)) (z : K) : f (σ * τ) z = f σ (f τ z) := by
    change (d (σ * τ) : K) * σ (τ z) = (d σ : K) * σ ((d τ : K) * τ z)
    rw [hd, Units.val_mul, map_mul]
    change ((d σ : K) * σ (d τ : K)) * σ (τ z) = _
    rw [mul_assoc]
  let ρ : Descent.SemilinearAction F K K :=
    { act := fun σ =>
        { toFun := f σ
          invFun := f σ⁻¹
          left_inv := fun z => by rw [← hmul, inv_mul_cancel, hone]
          right_inv := fun z => by rw [← hmul, mul_inv_cancel, hone]
          map_add' := fun z w => by simp [f, mul_add] }
      one_act := hone
      mul_act := hmul
      map_smul := fun σ c z => by
        change (d σ : K) * σ (c * z) = σ c * ((d σ : K) * σ z)
        rw [map_mul, mul_left_comm] }
  have hspan := Descent.SemilinearAction.span_fixed_eq_top ρ
  have h : ∃ z : K, z ∈ ρ.fixed ∧ z ≠ 0 := by
    by_contra! h
    have hbot : Submodule.span K (ρ.fixed : Set K) ≤ ⊥ :=
      Submodule.span_le.mpr fun z hz => (Submodule.mem_bot K).mpr (h z hz)
    rw [hspan] at hbot
    exact (top_ne_bot : (⊤ : Submodule K K) ≠ ⊥) (bot_unique hbot)
  obtain ⟨z, hz, hn⟩ := h
  refine ⟨Units.mk0 z hn, fun σ => Units.ext ?_⟩
  exact hz σ


open private rankOneCoroot from LinearAlgebraicGroups.Arithmetic.QuasiSplitOrbitPinnedModels
open private scaleMatrixIso scaleMatrixGroup scaleMatrixDiagonal scaleMatrixUpper scaleMatrixLower
  from LinearAlgebraicGroups.Arithmetic.TrialitarianFixedRootSL2

private theorem rankOneWeylRelation {R : Type u} [CommRing R] :
    let w := upper (1 : R) * lower (-1 : R) * upper 1
    w * upper 1 = lower (-1) * w := by
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;> simp [upper, lower, Matrix.mul_apply, Fin.sum_univ_two]

private theorem rankOne_inverseScales {p q : Kˣ}
    (h : let w := upper (p : K) * lower (-(q : K)) * upper (p : K)
      w * upper (p : K) = lower (-(q : K)) * w) : p * q = 1 := by
  let w := upper (p : K) * lower (-(q : K)) * upper (p : K)
  have he := congrArg (fun m : Matrix.SpecialLinearGroup (Fin 2) K => m.val 0 1) h
  change (w.val * (upper (p : K)).val) 0 1 = ((lower (-(q : K))).val * w.val) 0 1 at he
  have hz' : w.val 0 0 * (p : K) + w.val 0 1 = w.val 0 1 := by
    simpa [upper, lower, Matrix.mul_apply, Fin.sum_univ_two] using he
  have hz : w.val 0 0 * (p : K) = 0 := add_right_cancel (hz'.trans (zero_add _).symm)
  have hw : w.val 0 0 = 1 - (p : K) * (q : K) := by
    simp [w, upper, lower, Matrix.mul_apply, Fin.sum_univ_two, sub_eq_add_neg]
  apply Units.ext
  exact (sub_eq_zero.mp (hw.symm.trans ((mul_eq_zero.mp hz).resolve_right p.ne_zero))).symm

private theorem upper_transvection {R : Type u} [CommRing R] (x : R) :
    upper x = Matrix.SpecialLinearGroup.transvection (i := (0 : Fin 2)) (j := 1) (by decide) x := by
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;> simp [upper, Matrix.SpecialLinearGroup.transvection_coe]

private theorem lower_transvection {R : Type u} [CommRing R] (x : R) :
    lower x = Matrix.SpecialLinearGroup.transvection (i := (1 : Fin 2)) (j := 0) (by decide) x := by
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;> simp [lower, Matrix.SpecialLinearGroup.transvection_coe]

private theorem diagonal_rankOneCoroot {R : Type u} [CommRing R] (v : Rˣ) :
    diagonal v = rankOneCoroot v := by
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;> simp [diagonal, rankOneCoroot]

private theorem rootPoint_scale {A : AdditiveLine K} {B : GroupScheme K}
    (x : A.group ⟶ B) (v : Kˣ) (R : TestAlgebra K) (z : R) :
    rootPoint ((scaleIso A A v).hom ≫ x) R z = rootPoint x R (algebraMap K R (v : K) * z) := by
  rw [rootPoint_comp, scaleIso_point, rootPoint_eq]

open private SemilinearTestMap.commutes from LinearAlgebraicGroups.Arithmetic.QuasiSplitFixedWeyl

private theorem rootMark_rescale_fixed {B : GroupScheme F} {A : AdditiveLine K}
    (x : A.group ⟶ (groupBaseChange F K).obj B) (σ : Gal(K/F)) (d v : Kˣ)
    (hd : ∀ {R U : TestAlgebra K} (a : SemilinearTestMap σ R U) (z : R),
      semilinearPoint B a (rootPoint x R z) =
        rootPoint x U (algebraMap K U (d : K) * (SemilinearTestMap.restrict a).hom z))
    (hv : d * Units.map σ.toRingHom.toMonoidHom v = v)
    {R U : TestAlgebra K} (a : SemilinearTestMap σ R U) (z : R) :
    semilinearPoint B a (rootPoint ((scaleIso A A v).hom ≫ x) R z) =
      rootPoint ((scaleIso A A v).hom ≫ x) U ((SemilinearTestMap.restrict a).hom z) := by
  rw [rootPoint_scale, rootPoint_scale, hd]
  congr 1
  have hh : (SemilinearTestMap.restrict a).hom (algebraMap K R (v : K)) =
      algebraMap K U (σ (v : K)) := SemilinearTestMap.commutes a v
  rw [map_mul, hh, ← mul_assoc, ← map_mul]
  exact congrArg (fun t : Kˣ => algebraMap K U (t : K) *
    (SemilinearTestMap.restrict a).hom z) hv


private theorem rootMarks_inverseScales {B : GroupScheme F} {A : AdditiveLine K}
    {xPlus xMinus : A.group ⟶ (groupBaseChange F K).obj B}
    (m : rankOnePoints K ⟶ (groupPointsFunctor K).obj ((groupBaseChange F K).obj B))
    (hinj : Function.Injective (m.app (CommAlgCat.of K K)))
    (hu : ∀ z : K, m.app (CommAlgCat.of K K) (upper z) =
      rootPoint xPlus (CommAlgCat.of K K) z)
    (hl : ∀ z : K, m.app (CommAlgCat.of K K) (lower z) =
      rootPoint xMinus (CommAlgCat.of K K) z)
    (σ : Gal(K/F)) (p q : Kˣ)
    (hp : ∀ z : K, semilinearPoint B (semilinearFieldMap σ)
      (rootPoint xPlus (CommAlgCat.of K K) z) =
        rootPoint xPlus (CommAlgCat.of K K) ((p : K) * σ z))
    (hq : ∀ z : K, semilinearPoint B (semilinearFieldMap σ)
      (rootPoint xMinus (CommAlgCat.of K K) z) =
        rootPoint xMinus (CommAlgCat.of K K) ((q : K) * σ z)) :
    p * q = 1 := by
  let f : Matrix.SpecialLinearGroup (Fin 2) K →*
      GroupPoints ((groupBaseChange F K).obj B) (CommAlgCat.of K K) :=
    (m.app (CommAlgCat.of K K)).hom
  let s := semilinearPoint B (semilinearFieldMap σ)
  have hUpper : s (f (upper (1 : K))) = f (upper (p : K)) := by
    change s (m.app (CommAlgCat.of K K) (upper (1 : K))) =
      m.app (CommAlgCat.of K K) (upper (p : K))
    rw [hu, hu]
    change semilinearPoint B (semilinearFieldMap σ) (rootPoint xPlus (CommAlgCat.of K K) 1) = _
    simpa only [map_one, mul_one] using hp 1
  have hLower : s (f (lower (-1 : K))) = f (lower (-(q : K))) := by
    change s (m.app (CommAlgCat.of K K) (lower (-1 : K))) =
      m.app (CommAlgCat.of K K) (lower (-(q : K)))
    rw [hl, hl]
    change semilinearPoint B (semilinearFieldMap σ) (rootPoint xMinus (CommAlgCat.of K K) (-1)) = _
    simpa only [map_neg, map_one, mul_neg, mul_one] using hq (-1)
  have h := congrArg (fun g => s (f g)) (rankOneWeylRelation (R := K))
  simp only [map_mul, hUpper, hLower] at h
  apply rankOne_inverseScales
  change _ = _
  apply (show Function.Injective f from hinj)
  simpa only [map_mul] using h

private theorem rescaledMark_closed {A : AdditiveLine K} {B : GroupScheme K}
    (x : A.group ⟶ B) (hx : IsClosedImmersion x.hom.hom.left) (v : Kˣ) :
    IsClosedImmersion ((scaleIso A A v).hom ≫ x).hom.hom.left := by
  haveI : IsIso (scaleIso A A v).hom.hom.hom.left :=
    (Grp.forget (SchemeOver K) ⋙ Over.forget _).map_isIso (scaleIso A A v).hom
  letI := hx
  exact IsClosedImmersion.comp _ _

private theorem rescaledMark_action {A : AdditiveLine K} {B : GroupScheme K}
    {T : ClosedSubgroup B} {b : Character T.group}
    (x : A.group ⟶ B) (hx : HasScalarAction T b x) (v : Kˣ) :
    HasScalarAction T b ((scaleIso A A v).hom ≫ x) := by
  intro R t z
  rw [rootPoint_scale, rootPoint_scale, mul_left_comm (algebraMap K R (v : K))]
  exact hx R t (algebraMap K R (v : K) * z)

private theorem descendRootMark [IsGalois F K] {G : AffineAlgebraicGroup F}
    {A₀ : AdditiveLine F} {A : AdditiveLine K}
    (j : (groupBaseChange F K).obj A₀.group ≅ A.group)
    (hj : ∀ (R : TestAlgebra K) (z : R),
      baseChangePoint F K A₀.group.X R (rootPoint j.inv R z) =
        rootPoint (𝟙 A₀.group) ((restrictTestAlgebra F K).obj R) z)
    (x : A.group ⟶ (groupBaseChange F K).obj G.val)
    (hx : IsClosedImmersion x.hom.hom.left)
    (h : ∀ (σ : Gal(K/F)) {R U : TestAlgebra K} (a : SemilinearTestMap σ R U) (z : R),
      semilinearPoint G.val a (rootPoint x R z) =
        rootPoint x U ((SemilinearTestMap.restrict a).hom z)) :
    ∃ y : A₀.group ⟶ G.val, j.inv ≫ (groupBaseChange F K).map y = x ∧
      IsClosedImmersion y.hom.hom.left := by
  have hfix (σ : Gal(K/F)) : scalarMorphism σ (j.hom ≫ x) = j.hom ≫ x := by
    apply (cancel_epi j.inv).mp
    rw [Iso.inv_hom_id_assoc]
    apply Grp.hom_ext
    apply hom_ext_on_affine_tests
    intro U p
    obtain ⟨z, rfl⟩ := rootPoint_surjective (Iso.refl A.group) U p
    change rootPoint (𝟙 A.group) U z ≫ (j.inv ≫ scalarMorphism σ (j.hom ≫ x)).hom.hom =
      rootPoint (𝟙 A.group) U z ≫ x.hom.hom
    rw [← rootPoint_comp, ← rootPoint_comp, Category.id_comp, Category.id_comp]
    let a := semilinearSourceMap σ U
    exact (semilinear_rootMark j hj x a z).symm.trans (h σ a z)
  haveI : IsIso j.hom.hom.hom.left :=
    (Grp.forget (SchemeOver K) ⋙ Over.forget _).map_isIso j.hom
  letI := hx
  have hc : IsClosedImmersion (j.hom ≫ x).hom.hom.left := IsClosedImmersion.comp _ _
  obtain ⟨y, hy, hyc⟩ := descend_closedEmbedding (additiveLineGroup A₀) G (j.hom ≫ x) hc hfix
  exact ⟨y, by rw [hy, Iso.inv_hom_id_assoc], hyc⟩

theorem rootMarkNormalization : RootMarkNormalization.{u} := by
  intro F K _ _ _ _ _ G T hT
  dsimp only
  intro hG hs hm e he χ hb A xPlus xMinus hxPlus hxMinus haPlus haMinus D m hmInj hmUp hmLow hmDiag
  let E := groupBaseChange F K
  let TK := baseChangedSubgroup K T hT
  let b : Character TK.group := E.map χ ≫ e.inv
  change b ∈ absoluteRoots TK at hb
  change HasScalarAction TK b xPlus at haPlus
  change HasScalarAction TK b⁻¹ xMinus at haMinus
  have hbFixed (σ : Gal(K/F)) : scalarCharacter σ b = b := by
    let t := multiplicativeBaseChange F K
    have het : e = t := unitComparison_unique he (multiplicativeBaseChange_unit K)
    have hbt : b ≫ t.hom = E.map χ := by
      change (E.map χ ≫ e.inv) ≫ t.hom = _
      rw [het, Category.assoc, t.inv_hom_id, Category.comp_id]
    apply (cancel_mono t.hom).mp
    exact (scalarCharacter_comparison σ b).trans (by rw [hbt, scalarMorphism_baseChange])
  have hbInvFixed (σ : Gal(K/F)) : scalarCharacter σ b⁻¹ = b⁻¹ :=
    (map_inv (scalarCharacterEquiv σ T.group) b).trans (congrArg Inv.inv (hbFixed σ))
  have hbInv : b⁻¹ ∈ absoluteRoots TK := by
    have hr := (RootData.RootGroups.rootSubgroups _ hG TK hs hm).2 b hb |>.2.1 b⁻¹
    exact (hr.mpr (Or.inr rfl)).1
  obtain ⟨A₀⟩ := Classification.Pinning.additiveLineExists F
  obtain ⟨j, hj⟩ := additiveBaseChange A₀ A
  choose p hp using fun σ => fixedRoot_scales hT hG hs hm b hb j hj xPlus hxPlus haPlus σ (hbFixed σ)
  choose q hq using fun σ =>
    fixedRoot_scales hT hG hs hm b⁻¹ hbInv j hj xMinus hxMinus haMinus σ (hbInvFixed σ)
  have hpq (σ : Gal(K/F)) : p σ * q σ = 1 := by
    apply rootMarks_inverseScales m (hmInj (CommAlgCat.of K K))
      (hmUp (CommAlgCat.of K K)) (hmLow (CommAlgCat.of K K)) σ
    · intro z
      exact hp σ (semilinearFieldMap σ) z
    · intro z
      exact hq σ (semilinearFieldMap σ) z
  obtain ⟨v, hv⟩ := fixedScalar p (rootMark_scalarCocycle xPlus hxPlus p hp)
  have hvInv (σ : Gal(K/F)) : q σ * Units.map σ.toRingHom.toMonoidHom v⁻¹ = v⁻¹ := by
    have hqInv : q σ = (p σ)⁻¹ := by
      rw [← one_mul (q σ), ← inv_mul_cancel (p σ), mul_assoc, hpq, mul_one]
    rw [hqInv, map_inv, ← mul_inv_rev, mul_comm, hv]
  let uPlus := (scaleIso A A v).hom ≫ xPlus
  let uMinus := (scaleIso A A v⁻¹).hom ≫ xMinus
  obtain ⟨yPlus, hyPlus, hyPlusClosed⟩ := descendRootMark j hj uPlus
    (rescaledMark_closed xPlus hxPlus v)
    (fun σ _ _ a z => rootMark_rescale_fixed xPlus σ (p σ) v (hp σ) (hv σ) a z)
  obtain ⟨yMinus, hyMinus, hyMinusClosed⟩ := descendRootMark j hj uMinus
    (rescaledMark_closed xMinus hxMinus v⁻¹)
    (fun σ _ _ a z => rootMark_rescale_fixed xMinus σ (q σ) v⁻¹ (hq σ) (hvInv σ) a z)
  refine ⟨A₀, j, yPlus, yMinus, hj, hyPlusClosed, hyMinusClosed, ?_⟩
  rw [hyPlus, hyMinus]
  refine ⟨rescaledMark_action xPlus haPlus v, rescaledMark_action xMinus haMinus v⁻¹,
    (scaleMatrixIso v).hom ≫ m, ?_, ?_, ?_, ?_⟩
  · intro R
    exact (hmInj R).comp (ConcreteCategory.bijective_of_isIso ((scaleMatrixIso v).hom.app R)).injective
  · intro R z
    change m.app R (scaleMatrixGroup (Units.map (algebraMap K R : K →* R) v) (upper z)) =
      rootPoint uPlus R z
    rw [show scaleMatrixGroup (Units.map (algebraMap K R : K →* R) v) (upper z) =
      upper (algebraMap K R (v : K) * z) by
        rw [upper_transvection, upper_transvection]
        exact scaleMatrixUpper (Units.map (algebraMap K R : K →* R) v) z, hmUp]
    exact (rootPoint_scale xPlus v R z).symm
  · intro R z
    change m.app R (scaleMatrixGroup (Units.map (algebraMap K R : K →* R) v) (lower z)) =
      rootPoint uMinus R z
    rw [show scaleMatrixGroup (Units.map (algebraMap K R : K →* R) v) (lower z) =
      lower (algebraMap K R (↑v⁻¹ : K) * z) by
        rw [lower_transvection, lower_transvection]
        exact scaleMatrixLower (Units.map (algebraMap K R : K →* R) v) z, hmLow]
    exact (rootPoint_scale xMinus v⁻¹ R z).symm
  · intro R z
    change m.app R (scaleMatrixGroup (Units.map (algebraMap K R : K →* R) v) (diagonal z)) = _
    rw [show scaleMatrixGroup (Units.map (algebraMap K R : K →* R) v) (diagonal z) =
      diagonal z by simpa only [diagonal_rankOneCoroot] using scaleMatrixDiagonal _ z, hmDiag]

end

end LinearAlgebraicGroups.Arithmetic.LocalMixingRootMarkNormalization
