import MathGenome.Internal.RepresentationTheoryDeepening.Specs.RepTheorySurvey.Geometric.MiddleExtension
import MathGenome.Internal.RepresentationTheoryDeepening.RepTheorySurvey.Geometric.DerivedLocalSheaves
import Mathlib.RingTheory.Finiteness.Basic
import Batteries.Tactic.OpenPrivate

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open Topology TopologicalSpace Opposite
open scoped ZeroObject

universe u

namespace RepTheorySurvey.Geometric.MiddleExtension

open Analytic Analytic.IntersectionComplex LocalSheaf
open DerivedLocalSheaves (derivedInverseDirectAdjunctionData derivedExtraordinaryAdjunctionData)

open private existsInjectiveRepresentative exactPlusFactors exactDerivedCohomologyIso
  plusHomologyFactors cochainAdjunction exactRightDerivedAdjunction
  from MathGenome.Internal.RepresentationTheoryDeepening.RepTheorySurvey.Geometric.DerivedLocalSheaves

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
set_option linter.style.haveILetI false

private def exactCohomologyIso {C D : Type*} [Category* C] [Category* D]
    [Abelian C] [Abelian D] [HasDerivedCategory C] [HasDerivedCategory D] [EnoughInjectives C]
    (L : C ⥤ D) [L.Additive] [PreservesFiniteLimits L] [PreservesFiniteColimits L]
    (F : DerivedCategory.Plus C) (q : ℤ) :
    (DerivedCategory.Plus.homologyFunctor D q).obj ((exactDerivedPlus L).obj F) ≅
      L.obj ((DerivedCategory.Plus.homologyFunctor C q).obj F) := by
  let I := Classical.choose (existsInjectiveRepresentative F)
  let e := Classical.choice (Classical.choose_spec (existsInjectiveRepresentative F))
  let K := injectiveComplex I
  let HC := DerivedCategory.Plus.homologyFunctor C q
  let HD := DerivedCategory.Plus.homologyFunctor D q
  exact (HD.mapIso ((exactDerivedPlus L).mapIso e)).symm ≪≫ exactDerivedCohomologyIso L K q ≪≫
    L.mapIso (((plusHomologyFactors C q).app K).symm ≪≫ HC.mapIso e)

private def pullbackCohomologyIso {U X : TopCat.{u}} (j : U ⟶ X) (F : BoundedBelow X)
    (q : ℤ) : (cohomology U q).obj ((boundedBelowInverseImage j).obj F).obj ≅
      (inverseImage j).obj ((cohomology X q).obj F.obj) :=
  exactCohomologyIso (inverseImage j) F q

private instance pullbackCommShift {U X : TopCat.{u}} (j : U ⟶ X) :
    (boundedBelowInverseImage j).CommShift ℤ := by
  unfold boundedBelowInverseImage derivedInverseImage
  infer_instance

private instance pullbackTriangulated {U X : TopCat.{u}} (j : U ⟶ X) :
    (boundedBelowInverseImage j).IsTriangulated := by
  unfold boundedBelowInverseImage derivedInverseImage
  infer_instance

private instance shriekCommShift {X : TopCat.{u}} {Z : Set X} (hZ : IsClosed Z) :
    (derivedExtraordinaryInverseImage hZ).CommShift ℤ := by
  unfold derivedExtraordinaryInverseImage
  infer_instance

private instance shriekTriangulated {X : TopCat.{u}} {Z : Set X} (hZ : IsClosed Z) :
    (derivedExtraordinaryInverseImage hZ).IsTriangulated := by
  unfold derivedExtraordinaryInverseImage
  infer_instance

private theorem plusIsLE_iff {X : TopCat.{u}} (F : BoundedBelow X) (a : ℤ) :
    F.IsLE a ↔ ∀ q : ℤ, a < q → IsZero ((cohomology X q).obj F.obj) :=
  (DerivedCategory.Plus.isLE_ι_obj_iff F a).symm.trans (DerivedCategory.isLE_iff F.obj a)

private theorem plusIsGE_iff {X : TopCat.{u}} (F : BoundedBelow X) (a : ℤ) :
    F.IsGE a ↔ ∀ q : ℤ, q < a → IsZero ((cohomology X q).obj F.obj) :=
  (DerivedCategory.Plus.isGE_ι_obj_iff F a).symm.trans (DerivedCategory.isGE_iff F.obj a)

private theorem pullbackIsLE {U X : TopCat.{u}} (j : U ⟶ X) (F : BoundedBelow X) (a : ℤ)
    (h : F.IsLE a) : ((boundedBelowInverseImage j).obj F).IsLE a :=
  (plusIsLE_iff _ _).mpr fun q hq =>
    ((inverseImage j).map_isZero ((plusIsLE_iff F a).mp h q hq)).of_iso
      (pullbackCohomologyIso j F q)

private theorem pullbackIsGE {U X : TopCat.{u}} (j : U ⟶ X) (F : BoundedBelow X) (a : ℤ)
    (h : F.IsGE a) : ((boundedBelowInverseImage j).obj F).IsGE a :=
  (plusIsGE_iff _ _).mpr fun q hq =>
    ((inverseImage j).map_isZero ((plusIsGE_iff F a).mp h q hq)).of_iso
      (pullbackCohomologyIso j F q)

private def rightDerivedExactIso {C D : Type*} [Category* C] [Category* D]
    [Abelian C] [Abelian D] [HasDerivedCategory C] [HasDerivedCategory D] [EnoughInjectives C]
    (R : C ⥤ D) [R.Additive] [PreservesFiniteLimits R] [PreservesFiniteColimits R] :
    R.rightDerivedFunctorPlus ≅ exactDerivedPlus R := by
  let W := CochainComplex.Plus.quasiIso C
  let β := (exactPlusFactors R).symm
  letI : (exactDerivedPlus R).IsRightDerivedFunctor β.hom W :=
    Functor.isRightDerivedFunctor_of_inverts W _ β.symm
  exact Functor.rightDerivedUnique _ _ R.rightDerivedFunctorPlusUnit β.hom W

private def closedInverseAdjunction {X : TopCat.{u}} {Z : Set X} (hZ : IsClosed Z) :
    boundedBelowInverseImage (closedInclusion Z) ⊣ closedExtensionPlus hZ := by
  letI := (extraordinaryAdjunction hZ).isLeftAdjoint
  exact (derivedInverseDirectAdjunctionData (closedInclusion Z)).ofNatIsoRight
    (rightDerivedExactIso (directImage (closedInclusion Z)))

private instance closedExtensionAdditive {X : TopCat.{u}} {Z : Set X} (hZ : IsClosed Z) :
    (closedExtensionPlus hZ).Additive := by
  unfold closedExtensionPlus exactDerivedPlus
  infer_instance

private theorem openCounitIsIso {U X : TopCat.{u}} {j : U ⟶ X} (hj : IsOpenEmbedding j)
    (a : boundedBelowInverseImage j ⊣ derivedDirectImage j) (F : BoundedBelow U) :
    IsIso (a.counit.app F) := by
  let L := inverseImage j
  let R := directImage j
  let t := inverseDirectAdjunction j
  let A := exactDerivedPlus L
  let base : boundedBelowInverseImage j ⊣ derivedDirectImage j := exactRightDerivedAdjunction t
  have hbase : IsIso (base.counit.app F) := by
    obtain ⟨I, ⟨e⟩⟩ := existsInjectiveRepresentative F
    rw [← NatTrans.isIso_app_iff_of_iso base.counit e]
    let K := injectiveComplex I
    let Q := DerivedCategory.Plus.Q (C := Sheaves U)
    let α := exactPlusFactors L
    let β := R.rightDerivedFunctorPlusUnit
    let c := (cochainAdjunction t).counit.app K
    haveI (n : ℤ) : IsIso (c.hom.f n) := inducedCounit_isIso hj.isInducing (K.obj.X n)
    haveI : IsIso ((CochainComplex.Plus.ι (Sheaves U)).map c) :=
      HomologicalComplex.Hom.isIso_of_components c.hom
    haveI : IsIso c :=
      (CochainComplex.Plus.fullyFaithfulι (Sheaves U)).isIso_of_isIso_map c
    haveI : A.IsLeftAdjoint := base.isLeftAdjoint
    have h := (cochainAdjunction t).derivedε_fac_app
      (CochainComplex.Plus.quasiIso (Sheaves U)) α.hom β K
    change A.map (β.app K) ≫ base.counit.app (Q.obj K) =
      α.hom.app (R.mapCochainComplexPlus.obj K) ≫ Q.map c at h
    haveI : IsIso (β.app K) := inferInstanceAs
      (IsIso ((directImage j).rightDerivedFunctorPlusUnit.app (injectiveComplex I)))
    haveI : IsIso (A.map (β.app K)) := A.map_isIso _
    haveI : IsIso (A.map (β.app K) ≫ base.counit.app (Q.obj K)) := by rw [h]; infer_instance
    exact IsIso.of_isIso_comp_left (A.map (β.app K)) _
  haveI : IsIso ((boundedBelowInverseImage j).map ((base.rightAdjointUniq a).hom.app F)) :=
    (boundedBelowInverseImage j).map_isIso _
  haveI : IsIso ((boundedBelowInverseImage j).map ((base.rightAdjointUniq a).hom.app F) ≫
      a.counit.app F) := by
    rw [base.rightAdjointUniq_hom_app_counit a]
    exact hbase
  exact IsIso.of_isIso_comp_left
    ((boundedBelowInverseImage j).map ((base.rightAdjointUniq a).hom.app F)) _

theorem strictExtensionNoSupportedMorphisms : IntersectionComplex.Expected.StrictExtensionNoSupportedMorphisms.{u} := by
  intro U X j hj s F G hF hGge hGle
  obtain ⟨hstar, hshriek⟩ := hF
  let hZ := boundary_isClosed hj
  let left := closedInverseAdjunction hZ
  let right := derivedExtraordinaryAdjunctionData hZ
  constructor
  · intro f
    apply (right.homEquiv G F).injective
    rw [right.homAddEquiv_zero]
    exact DerivedCategory.Plus.TStructure.t.zero_of_isLE_of_isGE _ (-(s : ℤ))
      (-(s : ℤ) + 1) (by omega) hGle hshriek
  · intro g
    apply (left.homEquiv F G).symm.injective
    rw [left.homAddEquiv_symm_zero]
    exact DerivedCategory.Plus.TStructure.t.zero_of_isLE_of_isGE _ (-(s : ℤ) - 1)
      (-(s : ℤ)) (by omega) hstar hGge

private theorem derivedIsZero {X : TopCat.{u}} (F : BoundedBelow X)
    (h : ∀ q : ℤ, IsZero ((cohomology X q).obj F.obj)) : IsZero F := by
  haveI : IsIso (0 : F ⟶ 0) := (DerivedCategory.Plus.isIso_iff _).mpr fun q =>
    (h q).isIso ((DerivedCategory.Plus.homologyFunctor _ q).map_isZero (isZero_zero _)) _
  exact (isZero_zero _).of_iso (asIso (0 : F ⟶ 0))

private def pullbackStalkIso {U X : TopCat.{u}} (j : U ⟶ X) (F : BoundedBelow X)
    (q : ℤ) (x : U) :
    (stalk x).obj ((cohomology U q).obj ((boundedBelowInverseImage j).obj F).obj) ≅
      (stalk (j x)).obj ((cohomology X q).obj F.obj) :=
  (stalk x).mapIso (pullbackCohomologyIso j F q) ≪≫
    (inverseImageStalkIso j ((cohomology X q).obj F.obj) x).symm

private theorem supported_iff_restrictionZero {U X : TopCat.{u}} (j : U ⟶ X)
    (F : BoundedBelow X) : DerivedSupportedOn (boundary j) F ↔
      IsZero ((boundedBelowInverseImage j).obj F) := by
  constructor
  · intro h
    refine derivedIsZero _ fun q => (TopCat.Sheaf.isZero_iff_stalkFunctor_obj_isZero _).mpr ?_
    intro x
    exact (h q (j x) (by simp [boundary])).of_iso (pullbackStalkIso j F q x)
  · intro h q x hx
    obtain ⟨y, rfl⟩ : x ∈ Set.range j := by simpa only [boundary, Set.mem_compl_iff, not_not] using hx
    exact ((cohomology U q ⋙ stalk y).map_isZero
      (DerivedCategory.Plus.ι.map_isZero h)).of_iso (pullbackStalkIso j F q y).symm

private theorem shriekDirectImageZero {U X : TopCat.{u}} {j : U ⟶ X} (hj : IsOpenEmbedding j)
    (F : BoundedBelow U) :
    IsZero ((derivedExtraordinaryInverseImage (boundary_isClosed hj)).obj
      ((derivedDirectImage j).obj F)) := by
  let hZ := boundary_isClosed hj
  let G := (derivedDirectImage j).obj F
  let C := (derivedExtraordinaryInverseImage hZ).obj G
  let a := derivedExtraordinaryAdjunctionData hZ
  let b := derivedInverseDirectAdjunctionData j
  have hz : IsZero ((boundedBelowInverseImage j).obj ((closedExtensionPlus hZ).obj C)) :=
    (supported_iff_restrictionZero j _).mp
      ((DerivedLocalSheaves.derivedSupportedEssentialImage hZ _).mp ⟨C, ⟨Iso.refl _⟩⟩)
  have h : (a.homEquiv C G).symm (𝟙 C) = 0 := by
    apply (b.homEquiv _ F).symm.injective
    exact hz.eq_of_src _ _
  rw [IsZero.iff_id_eq_zero]
  apply (a.homEquiv C G).symm.injective
  rw [h, a.homAddEquiv_symm_zero]

private def supportedShriekIso {X : TopCat.{u}} {Z : Set X} (hZ : IsClosed Z)
    {C : BoundedBelow X} {D : BoundedBelow (TopCat.of Z)}
    (e : (closedExtensionPlus hZ).obj D ≅ C) :
    D ≅ (derivedExtraordinaryInverseImage hZ).obj C := by
  let ff := Classical.choice (DerivedLocalSheaves.derivedClosedExtensionFullyFaithful hZ)
  haveI := ff.full
  haveI := ff.faithful
  let a := derivedExtraordinaryAdjunctionData hZ
  exact asIso (a.unit.app D) ≪≫ (derivedExtraordinaryInverseImage hZ).mapIso e

private theorem shriekIsGE_of_triangle {U X : TopCat.{u}} {j : U ⟶ X} (hj : IsOpenEmbedding j)
    (T : Triangle (BoundedBelow X)) (hT : T ∈ distTriang (BoundedBelow X))
    (h₂ : IsZero ((derivedExtraordinaryInverseImage (boundary_isClosed hj)).obj T.obj₂))
    (b : ℤ)
    (h₃ : ((derivedExtraordinaryInverseImage (boundary_isClosed hj)).obj T.obj₃).IsGE b) :
    ((derivedExtraordinaryInverseImage (boundary_isClosed hj)).obj T.obj₁).IsGE (b + 1) := by
  let R := derivedExtraordinaryInverseImage (boundary_isClosed hj)
  let S := R.mapTriangle.obj T
  haveI : IsIso S.mor₃ := (S.isZero₂_iff_isIso₃ (R.map_distinguished T hT)).mp h₂
  let t := DerivedCategory.Plus.TStructure.t (C := Sheaves (TopCat.of (boundary j)))
  haveI : t.IsGE S.obj₃ b := h₃
  haveI : t.IsGE ((R.obj T.obj₁)⟦(1 : ℤ)⟧) b := t.isGE_of_iso (asIso S.mor₃) b
  exact t.isGE_of_shift _ (b + 1) 1 b (by omega)

private theorem restrictedUnitIsIso {U X : TopCat.{u}} {j : U ⟶ X} (hj : IsOpenEmbedding j)
    (B : BoundedBelow X) :
    IsIso ((boundedBelowInverseImage j).map ((derivedInverseDirectAdjunctionData j).unit.app B)) := by
  let a := derivedInverseDirectAdjunctionData j
  let L := boundedBelowInverseImage j
  haveI : IsIso (a.counit.app (L.obj B)) := openCounitIsIso hj a _
  haveI : IsIso (L.map (a.unit.app B) ≫ a.counit.app (L.obj B)) := by
    rw [a.left_triangle_components B]
    exact (Iso.refl _).isIso_hom
  exact IsIso.of_isIso_comp_right _ (a.counit.app (L.obj B))

private theorem homToSupportedEqZero {X : TopCat.{u}} {Z : Set X} (hZ : IsClosed Z)
    {A C : BoundedBelow X} {D : BoundedBelow (TopCat.of Z)}
    (e : (closedExtensionPlus hZ).obj D ≅ C) (b c : ℤ) (hbc : b < c)
    (hA : ((boundedBelowInverseImage (closedInclusion Z)).obj A).IsLE b)
    (hD : D.IsGE c) (f : A ⟶ C) : f = 0 := by
  have h : f ≫ e.inv = 0 := by
    let a := closedInverseAdjunction hZ
    apply (a.homEquiv A D).symm.injective
    rw [a.homAddEquiv_symm_zero]
    exact DerivedCategory.Plus.TStructure.t.zero_of_isLE_of_isGE _ b c hbc hA hD
  exact (cancel_mono e.inv).mp (by simpa only [zero_comp] using h)

/-- The cone of the restriction unit is supported on the boundary. The two degree
bounds make its relevant Hom groups vanish. -/
private theorem strictMapBijective {U X : TopCat.{u}} {j : U ⟶ X} (hj : IsOpenEmbedding j)
    (s : ℕ) {A B : BoundedBelow X} (hA : IsStrictExtension hj s A)
    (hB : IsStrictExtension hj s B) :
    Function.Bijective (fun f : A ⟶ B => (boundedBelowInverseImage j).map f) := by
  let L := boundedBelowInverseImage j
  let a := derivedInverseDirectAdjunctionData j
  let hZ := boundary_isClosed hj
  let R := derivedExtraordinaryInverseImage hZ
  let b : ℤ := -(s : ℤ)
  let t := DerivedCategory.Plus.TStructure.t (C := Sheaves (TopCat.of (boundary j)))
  obtain ⟨C, g, δ, hT⟩ := distinguished_cocone_triangle (a.unit.app B)
  let T := Triangle.mk (a.unit.app B) g δ
  have hz : IsZero (L.obj C) :=
    (L.mapTriangle.obj T).isZero₃_of_isIso₁ (L.map_distinguished T hT) (restrictedUnitIsIso hj B)
  obtain ⟨D, ⟨e⟩⟩ := (DerivedLocalSheaves.derivedSupportedEssentialImage hZ _).mpr
    ((supported_iff_restrictionZero j C).mpr hz)
  let S := R.mapTriangle.obj T
  haveI : IsIso S.mor₃ := (S.isZero₂_iff_isIso₃ (R.map_distinguished T hT)).mp
    (shriekDirectImageZero hj (L.obj B))
  haveI : t.IsGE (R.obj B) (b + 1) := hB.2
  haveI : t.IsGE ((R.obj B)⟦(1 : ℤ)⟧) b := t.isGE_shift _ (b + 1) 1 b (by omega)
  haveI : t.IsGE (S.obj₁⟦(1 : ℤ)⟧) b := inferInstanceAs (t.IsGE ((R.obj B)⟦(1 : ℤ)⟧) b)
  haveI hD : D.IsGE b := t.isGE_of_iso (supportedShriekIso hZ e ≪≫ asIso S.mor₃).symm b
  have h₁ (f : A ⟶ C) : f = 0 :=
    homToSupportedEqZero hZ e (b - 1) b (by omega) hA.1 hD f
  haveI hD' : (D⟦(-1 : ℤ)⟧).IsGE (b + 1) := t.isGE_shift D b (-1) _ (by omega)
  have h₂ (f : A ⟶ T.invRotate.obj₁) : f = 0 := by
    haveI : (closedExtensionPlus hZ).CommShift ℤ := by
      unfold closedExtensionPlus exactDerivedPlus
      infer_instance
    let e' := ((closedExtensionPlus hZ).commShiftIso (-1 : ℤ)).app D ≪≫
      (shiftFunctor _ (-1 : ℤ)).mapIso e
    exact homToSupportedEqZero hZ e' (b - 1) (b + 1) (by omega) hA.1 hD' f
  have hbij : Function.Bijective (fun f : A ⟶ B => f ≫ a.unit.app B) := by
    constructor
    · intro f₁ f₂ hh
      have hh' : (f₁ - f₂) ≫ T.invRotate.mor₂ = 0 := by
        change (f₁ - f₂) ≫ a.unit.app B = 0
        change f₁ ≫ a.unit.app B = f₂ ≫ a.unit.app B at hh
        rw [Preadditive.sub_comp, hh, sub_self]
      obtain ⟨k, hk⟩ := T.invRotate.coyoneda_exact₂ (inv_rot_of_distTriang T hT) _ hh'
      apply sub_eq_zero.mp
      rw [hk, h₂ k, zero_comp]
    · intro f
      obtain ⟨k, hk⟩ := T.coyoneda_exact₂ hT f (h₁ _)
      exact ⟨k, hk.symm⟩
  have hh (f : A ⟶ B) :
      a.homEquiv A (L.obj B) (L.map f) = f ≫ a.unit.app B := by
    rw [Adjunction.homEquiv_unit]
    exact (a.unit.naturality f).symm
  have he : (fun f : A ⟶ B => L.map f) =
      (a.homEquiv A (L.obj B)).symm ∘ (fun f => f ≫ a.unit.app B) := by
    funext f
    exact (Equiv.eq_symm_apply _).mpr (hh f)
  rw [he]
  exact (a.homEquiv A (L.obj B)).symm.bijective.comp hbij

theorem strictRestrictionFullyFaithful :
    IntersectionComplex.Expected.StrictRestrictionFullyFaithful.{u} := by
  intro U X j hj s
  have h {A B : (show ObjectProperty (BoundedBelow X) from IsStrictExtension hj s).FullSubcategory} :
      Function.Bijective (fun f : A ⟶ B => (strictRestriction hj s).map f) :=
    (strictMapBijective hj s A.property B.property).comp
      (ObjectProperty.fullyFaithfulι _).homEquiv.bijective
  letI : (strictRestriction hj s).Full := ⟨h.surjective⟩
  letI : (strictRestriction hj s).Faithful := ⟨fun hf => h.injective hf⟩
  exact ⟨Functor.FullyFaithful.ofFullyFaithful _⟩


/-- The ordinary truncation triangle lifted to bounded-below objects. -/
private def truncationTriangle {X : TopCat.{u}} (a : ℤ) (F : BoundedBelow X) :
    Triangle (BoundedBelow X) :=
  let t := DerivedCategory.TStructure.t (C := Sheaves X)
  let T := (t.triangleLEGT a).obj F.obj
  let C : BoundedBelow X := ⟨T.obj₃, ⟨a + 1, by
    change t.IsGE ((t.truncGE (a + 1)).obj F.obj) (a + 1)
    infer_instance⟩⟩
  let E := (truncLE X a).obj F
  Triangle.mk (X := E) (Y := F) (Z := C)
    (ObjectProperty.homMk T.mor₁) (ObjectProperty.homMk T.mor₂)
    (ObjectProperty.homMk (T.mor₃ ≫ ((DerivedCategory.Plus.ι (C := Sheaves X)).commShiftIso (1 : ℤ)).inv.app E))

private theorem truncationTriangle_distinguished {X : TopCat.{u}} (a : ℤ) (F : BoundedBelow X) :
    truncationTriangle a F ∈ distTriang (BoundedBelow X) := by
  change (DerivedCategory.Plus.ι.mapTriangle.obj (truncationTriangle a F)) ∈ distTriang (Derived X)
  let t := DerivedCategory.TStructure.t (C := Sheaves X)
  let T := (t.triangleLEGT a).obj F.obj
  let S := DerivedCategory.Plus.ι.mapTriangle.obj (truncationTriangle a F)
  have e : S ≅ T := Triangle.isoMk S T (Iso.refl _) (Iso.refl _) (Iso.refl _)
    (by change S.mor₁ ≫ 𝟙 _ = 𝟙 _ ≫ S.mor₁; simp)
    (by change S.mor₂ ≫ 𝟙 _ = 𝟙 _ ≫ S.mor₂; simp)
    (by
      change S.mor₃ ≫ (shiftFunctor (Derived X) (1 : ℤ)).map (𝟙 S.obj₁) =
        𝟙 S.obj₃ ≫ T.mor₃
      rw [(shiftFunctor (Derived X) (1 : ℤ)).map_id, Category.comp_id, Category.id_comp]
      change (_ ≫ ((DerivedCategory.Plus.ι (C := Sheaves X)).commShiftIso (1 : ℤ)).inv.app _) ≫
          ((DerivedCategory.Plus.ι (C := Sheaves X)).commShiftIso (1 : ℤ)).hom.app _ = _
      simp only [Category.assoc, Iso.inv_hom_id_app, Category.comp_id]
      rfl)
  exact (distinguished_iff_of_iso e).mpr (t.triangleLEGT_distinguished a F.obj)

private theorem truncationTriangle_isLE {X : TopCat.{u}} (a : ℤ) (F : BoundedBelow X) :
    (truncationTriangle a F).obj₁.IsLE a := by
  apply (DerivedCategory.Plus.isLE_ι_obj_iff _ _).mp
  exact (DerivedCategory.TStructure.t (C := Sheaves X)).isLE_truncLE_obj F.obj a a

private theorem truncationTriangle_isGE {X : TopCat.{u}} (a : ℤ) (F : BoundedBelow X) :
    (truncationTriangle a F).obj₃.IsGE (a + 1) := by
  apply (DerivedCategory.Plus.isGE_ι_obj_iff _ _).mp
  change DerivedCategory.TStructure.t.IsGE
    ((DerivedCategory.TStructure.t.truncGE (a + 1)).obj F.obj) (a + 1)
  infer_instance

private theorem pullbackTruncationZero {U X : TopCat.{u}} (j : U ⟶ X)
    (a : ℤ) (F : BoundedBelow X) (h : ((boundedBelowInverseImage j).obj F).IsLE a) :
    IsZero ((boundedBelowInverseImage j).obj (truncationTriangle a F).obj₃) := by
  let L := boundedBelowInverseImage j
  let T := L.mapTriangle.obj (truncationTriangle a F)
  let t := DerivedCategory.Plus.TStructure.t (C := Sheaves U)
  have hT := L.map_distinguished (truncationTriangle a F) (truncationTriangle_distinguished a F)
  haveI h₁ : t.IsLE T.obj₁ a := pullbackIsLE j _ _ (truncationTriangle_isLE a F)
  have h₃ : t.IsGE T.obj₃ (a + 1) := pullbackIsGE j _ _ (truncationTriangle_isGE a F)
  have h₂₃ : T.mor₂ = 0 := t.zero_of_isLE_of_isGE _ a (a + 1) (by omega) h h₃
  haveI hshift : t.IsLE (T.obj₁⟦(1 : ℤ)⟧) (a - 1) := t.isLE_shift T.obj₁ a 1 _ (by omega)
  rw [show L.obj (truncationTriangle a F).obj₃ = T.obj₃ from rfl, IsZero.iff_id_eq_zero]
  obtain ⟨f, hf⟩ := T.yoneda_exact₃ hT (𝟙 T.obj₃) (by rw [Category.comp_id, h₂₃])
  rw [hf, t.zero_of_isLE_of_isGE f (a - 1) (a + 1) (by omega) hshift h₃, comp_zero]

private theorem strictAttachmentOfBound {U X : TopCat.{u}} (j : U ⟶ X) (hj : IsOpenEmbedding j)
    (s : ℕ) (F : BoundedBelow U) (hF : F.IsLE (-(s : ℤ) - 1)) :
    IsStrictExtension hj s ((attachment j hj s).obj F) ∧
      ∀ a : boundedBelowInverseImage j ⊣ derivedDirectImage j,
        IsIso ((boundedBelowInverseImage j).map ((attachmentInclusion j hj s).app F) ≫
          a.counit.app F) := by
  let b : ℤ := -(s : ℤ)
  let G := (derivedDirectImage j).obj F
  let T := truncationTriangle (b - 1) G
  let L := boundedBelowInverseImage j
  let hZ := boundary_isClosed hj
  let R := derivedExtraordinaryInverseImage hZ
  let a := derivedInverseDirectAdjunctionData j
  haveI : IsIso (a.counit.app F) := openCounitIsIso hj a F
  let t := DerivedCategory.Plus.TStructure.t (C := Sheaves U)
  haveI : t.IsLE F (b - 1) := hF
  haveI : t.IsLE ((𝟭 (BoundedBelow U)).obj F) (b - 1) := hF
  have hG : (L.obj G).IsLE (b - 1) := t.isLE_of_iso (asIso (a.counit.app F)).symm _
  have hz : IsZero (L.obj T.obj₃) := pullbackTruncationZero j _ G hG
  have hT : T ∈ distTriang (BoundedBelow X) := truncationTriangle_distinguished _ G
  haveI hι : IsIso (L.map T.mor₁) :=
    ((L.mapTriangle.obj T).isZero₃_iff_isIso₁ (L.map_distinguished T hT)).mp hz
  refine ⟨⟨pullbackIsLE _ _ _ (truncationTriangle_isLE _ G), ?_⟩, ?_⟩
  · obtain ⟨D, ⟨e⟩⟩ := (DerivedLocalSheaves.derivedSupportedEssentialImage hZ _).mpr
      ((supported_iff_restrictionZero j T.obj₃).mpr hz)
    have hc : T.obj₃.IsGE b := by simpa using truncationTriangle_isGE (b - 1) G
    let a' := closedInverseAdjunction hZ
    let ff := Classical.choice (DerivedLocalSheaves.derivedClosedExtensionFullyFaithful hZ)
    haveI := ff.full
    haveI := ff.faithful
    let I := boundedBelowInverseImage (closedInclusion (boundary j))
    have hIc : (I.obj T.obj₃).IsGE b := pullbackIsGE _ _ _ hc
    let t' := DerivedCategory.Plus.TStructure.t (C := Sheaves (TopCat.of (boundary j)))
    haveI : t'.IsGE (I.obj T.obj₃) b := hIc
    haveI : t'.IsGE D b := t'.isGE_of_iso ((I.mapIso e).symm ≪≫ asIso (a'.counit.app D)) _
    have hR : (R.obj T.obj₃).IsGE b := t'.isGE_of_iso (supportedShriekIso hZ e) _
    exact shriekIsGE_of_triangle hj T hT (shriekDirectImageZero hj F) b hR
  · intro a'
    haveI : IsIso (a'.counit.app F) := openCounitIsIso hj a' F
    change IsIso (L.map T.mor₁ ≫ a'.counit.app F)
    infer_instance

private theorem perverseIsLE {X : TopCat.{u}} (P : Stratification X) (F : BoundedBelow X)
    (s : ℕ) (hP : ∀ p : P.Index, s < (P.stratum p).complexDimension)
    (hF : IsMiddlePerverse P F.obj) : F.IsLE (-(s : ℤ) - 1) := by
  refine (plusIsLE_iff _ _).mpr fun q hq =>
    (TopCat.Sheaf.isZero_iff_stalkFunctor_obj_isZero _).mpr ?_
  intro x
  obtain ⟨p, hp, _⟩ := P.partition x
  obtain ⟨y, rfl⟩ := hp
  have h' : -((P.stratum p).complexDimension : ℤ) < q := by have := hP p; omega
  exact ((stalk y).map_isZero (hF.2.choose_spec p |>.1 q h')).of_iso
    (pullbackStalkIso (P.stratum p).inclusion F q y).symm

private def pullbackIdentityIso (X : TopCat.{u}) :
    boundedBelowInverseImage (𝟙 X) ≅ 𝟭 (BoundedBelow X) := by
  let f := inverseImage (𝟙 X)
  let e : f ≅ 𝟭 (Sheaves X) := (inverseDirectAdjunction (𝟙 X)).leftAdjointUniq Adjunction.id
  let a : f.mapDerivedCategory ≅ (𝟭 (Sheaves X)).mapDerivedCategory :=
    Localization.liftNatIso DerivedCategory.Q
      (HomologicalComplex.quasiIso (Sheaves X) (.up ℤ)) _ _ _ _
      (Functor.isoWhiskerRight (NatIso.mapHomologicalComplex e _) DerivedCategory.Q)
  let b := a ≪≫ Functor.mapDerivedCategoryIdIso (Sheaves X)
  refine NatIso.ofComponents
    (fun F => ObjectProperty.isoMk _ (b.app F.obj)) (fun g => ?_)
  apply ObjectProperty.hom_ext
  exact b.hom.naturality g.hom

private def pullbackEquivalence {X Y : TopCat.{u}} (e : X ≅ Y) :
    BoundedBelow Y ≌ BoundedBelow X :=
  CategoryTheory.Equivalence.mk (boundedBelowInverseImage e.hom) (boundedBelowInverseImage e.inv)
    ((pullbackIdentityIso Y).symm ≪≫
      eqToIso (congrArg (fun f => boundedBelowInverseImage f) e.inv_hom_id.symm) ≪≫
      boundedBelowPullbackComposition e.inv e.hom)
    ((boundedBelowPullbackComposition e.hom e.inv).symm ≪≫
      eqToIso (congrArg (fun f => boundedBelowInverseImage f) e.hom_inv_id) ≪≫
      pullbackIdentityIso X)

private def derivedDirectImageComposition {U V X : TopCat.{u}} (k : U ⟶ V) (j : V ⟶ X) :
    derivedDirectImage (k ≫ j) ≅ derivedDirectImage k ⋙ derivedDirectImage j :=
  ((derivedInverseDirectAdjunctionData (k ≫ j)).ofNatIsoLeft
    (boundedBelowPullbackComposition k j)).rightAdjointUniq
      ((derivedInverseDirectAdjunctionData j).comp (derivedInverseDirectAdjunctionData k))

private def derivedClosedDirectIso {X : TopCat.{u}} {Z : Set X} (hZ : IsClosed Z) :
    derivedDirectImage (closedInclusion Z) ≅ closedExtensionPlus hZ := by
  letI := (extraordinaryAdjunction hZ).isLeftAdjoint
  exact rightDerivedExactIso (directImage (closedInclusion Z))

private theorem disjointSupportedPullbackZero {X : TopCat.{u}} {Z : Set X}
    (hZ : IsClosed Z) {W : TopCat.{u}} (k : W ⟶ X) (h : Z ⊆ Set.range k)
    (F : BoundedBelow (TopCat.of Z)) :
    IsZero ((boundedBelowInverseImage (closedInclusion (boundary k))).obj
      ((closedExtensionPlus hZ).obj F)) := by
  let H := (closedExtensionPlus hZ).obj F
  have hs := (DerivedLocalSheaves.derivedSupportedEssentialImage hZ H).mp ⟨F, ⟨Iso.refl _⟩⟩
  refine derivedIsZero _ fun q => (TopCat.Sheaf.isZero_iff_stalkFunctor_obj_isZero _).mpr ?_
  intro x
  exact (hs q x.val (fun hx => x.property (h hx))).of_iso
    (pullbackStalkIso (closedInclusion (boundary k)) H q x)

private theorem shriekOfDisjointSupportZero {X W : TopCat.{u}} {Z : Set X} (hZ : IsClosed Z)
    {k : W ⟶ X} (hk : IsOpenEmbedding k) (h : Z ⊆ Set.range k) (C : BoundedBelow X)
    (hC : IsZero ((boundedBelowInverseImage k).obj C)) :
    IsZero ((derivedExtraordinaryInverseImage hZ).obj C) := by
  let D := (derivedExtraordinaryInverseImage hZ).obj C
  let a := derivedExtraordinaryAdjunctionData hZ
  let hV := boundary_isClosed hk
  let b := closedInverseAdjunction hV
  obtain ⟨E, ⟨e⟩⟩ := (DerivedLocalSheaves.derivedSupportedEssentialImage hV C).mpr
    ((supported_iff_restrictionZero k C).mpr hC)
  have hz := disjointSupportedPullbackZero hZ k h D
  rw [IsZero.iff_id_eq_zero]
  apply (a.homEquiv D C).symm.injective
  rw [a.homAddEquiv_symm_zero]
  apply (cancel_mono e.inv).mp
  rw [zero_comp]
  apply (b.homEquiv ((closedExtensionPlus hZ).obj D) E).symm.injective
  exact hz.eq_of_src _ _

/-- The extraordinary inverse image along a closed set can be computed after
restriction to any open neighborhood of that set. -/
private theorem shriekUnitIsIso {X W : TopCat.{u}} {Z : Set X} (hZ : IsClosed Z)
    {k : W ⟶ X} (hk : IsOpenEmbedding k) (h : Z ⊆ Set.range k) (F : BoundedBelow X) :
    IsIso ((derivedExtraordinaryInverseImage hZ).map
      ((derivedInverseDirectAdjunctionData k).unit.app F)) := by
  let a := derivedInverseDirectAdjunctionData k
  let L := boundedBelowInverseImage k
  let R := derivedExtraordinaryInverseImage hZ
  obtain ⟨C, g, δ, hT⟩ := distinguished_cocone_triangle (a.unit.app F)
  let T := Triangle.mk (a.unit.app F) g δ
  have hz : IsZero (L.obj C) :=
    (L.mapTriangle.obj T).isZero₃_of_isIso₁ (L.map_distinguished T hT) (restrictedUnitIsIso hk F)
  exact ((R.mapTriangle.obj T).isZero₃_iff_isIso₁ (R.map_distinguished T hT)).mp
    (shriekOfDisjointSupportZero hZ hk h C hz)

private def closedShriekOpenIso {X W : TopCat.{u}} {Z : Set X} {Y : Set W}
    (hZ : IsClosed Z) (hY : IsClosed Y) (k : W ⟶ X) (hk : IsOpenEmbedding k)
    (v : TopCat.of Z ≅ TopCat.of Y)
    (hv : v.hom ≫ closedInclusion Y ≫ k = closedInclusion Z)
    (F : BoundedBelow X) :
    (derivedExtraordinaryInverseImage hZ).obj F ≅
      (boundedBelowInverseImage v.hom).obj
        ((derivedExtraordinaryInverseImage hY).obj ((boundedBelowInverseImage k).obj F)) := by
  let V := pullbackEquivalence v
  let a := derivedInverseDirectAdjunctionData k
  let R := derivedExtraordinaryInverseImage hZ
  let L := boundedBelowInverseImage k
  let A := closedExtensionPlus hZ
  let B := closedExtensionPlus hY
  let d := derivedDirectImage k
  let m := closedInclusion Y
  have hsub : Z ⊆ Set.range k := by
    intro x hx
    let z : Z := ⟨x, hx⟩
    exact ⟨m (v.hom z), congrArg (fun f : TopCat.of Z ⟶ X => f z) hv⟩
  haveI (G : BoundedBelow W) : IsIso (a.counit.app G) := openCounitIsIso hk a G
  haveI : IsIso a.counit := NatIso.isIso_of_isIso_app _
  let ε : d ⋙ L ≅ 𝟭 (BoundedBelow W) := asIso a.counit
  let e₀ : derivedDirectImage v.hom ≅ V.inverse :=
    (derivedInverseDirectAdjunctionData v.hom).rightAdjointUniq V.toAdjunction
  let e₁ : A ≅ V.inverse ⋙ (B ⋙ d) :=
    (derivedClosedDirectIso hZ).symm ≪≫
    eqToIso (congrArg (fun f => derivedDirectImage f) hv.symm) ≪≫
    derivedDirectImageComposition v.hom (m ≫ k) ≪≫
    Functor.isoWhiskerLeft _ (derivedDirectImageComposition m k) ≪≫
    Functor.isoWhiskerLeft _ (Functor.isoWhiskerRight (derivedClosedDirectIso hY) _) ≪≫
    Functor.isoWhiskerRight e₀ _
  let e₂ : A ⋙ L ≅ V.inverse ⋙ B :=
    Functor.isoWhiskerRight e₁ _ ≪≫ Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft _ (Functor.associator _ _ _ ≪≫
        Functor.isoWhiskerLeft _ ε ≪≫ Functor.rightUnitor _)
  let c := ((derivedExtraordinaryAdjunctionData hZ).comp a).ofNatIsoLeft e₂
  let d' := V.symm.toAdjunction.comp (derivedExtraordinaryAdjunctionData hY)
  haveI : IsIso (R.map (a.unit.app F)) := shriekUnitIsIso hZ hk hsub F
  exact asIso (R.map (a.unit.app F)) ≪≫ (c.rightAdjointUniq d').app (L.obj F)

private theorem stratumEmbedding {X : TopCat.{u}} (S : Stratum X) : IsEmbedding S.inclusion :=
  S.ambientOpen.isOpenEmbedding.isEmbedding.comp IsEmbedding.subtypeVal

private def liftAlongEmbedding {A B X : TopCat.{u}} (f : A ⟶ X) (g : B ⟶ X)
    (hg : IsEmbedding g) (h : Set.range f ⊆ Set.range g) : A ⟶ B :=
  TopCat.ofHom ⟨fun x => hg.toHomeomorph.symm ⟨f x, h ⟨x, rfl⟩⟩,
    hg.toHomeomorph.symm.continuous.comp (f.hom.continuous.subtype_mk _)⟩

private theorem liftAlongEmbedding_comp {A B X : TopCat.{u}} (f : A ⟶ X) (g : B ⟶ X)
    (hg : IsEmbedding g) (h : Set.range f ⊆ Set.range g) :
    liftAlongEmbedding f g hg h ≫ g = f := by
  apply TopCat.ext
  intro x
  change g (hg.toHomeomorph.symm ⟨f x, _⟩) = f x
  exact congrArg Subtype.val (hg.toHomeomorph.apply_symm_apply ⟨f x, _⟩)

private def embeddingIsoOfRange {A B X : TopCat.{u}} (f : A ⟶ X) (g : B ⟶ X)
    (hf : IsEmbedding f) (hg : IsEmbedding g) (h : Set.range f = Set.range g) : A ≅ B :=
  TopCat.isoOfHomeo (hf.toHomeomorph.trans ((Homeomorph.setCongr h).trans hg.toHomeomorph.symm))

private theorem embeddingIsoOfRange_comp {A B X : TopCat.{u}} (f : A ⟶ X) (g : B ⟶ X)
    (hf : IsEmbedding f) (hg : IsEmbedding g) (h : Set.range f = Set.range g) :
    (embeddingIsoOfRange f g hf hg h).hom ≫ g = f :=
  liftAlongEmbedding_comp f g hg h.le

private theorem cohomologyIsZero_pullback_iff {A B : TopCat.{u}} (e : A ≅ B)
    (F : BoundedBelow B) (q : ℤ) :
    IsZero ((cohomology A q).obj ((boundedBelowInverseImage e.hom).obj F).obj) ↔
      IsZero ((cohomology B q).obj F.obj) := by
  constructor
  · intro hz
    apply (TopCat.Sheaf.isZero_iff_stalkFunctor_obj_isZero _).mpr
    intro x
    let y := e.inv x
    have hy : e.hom y = x := congrArg (fun f : B ⟶ B => f x) e.inv_hom_id
    rw [← hy]
    exact ((stalk y).map_isZero hz).of_iso (pullbackStalkIso e.hom F q y).symm
  · intro hz
    exact ((inverseImage e.hom).map_isZero hz).of_iso (pullbackCohomologyIso e.hom F q)

private theorem cohomologyIsZero_iso_iff {X : TopCat.{u}} {A B : BoundedBelow X}
    (e : A ≅ B) (q : ℤ) :
    IsZero ((cohomology X q).obj A.obj) ↔ IsZero ((cohomology X q).obj B.obj) := by
  let e' := (DerivedCategory.Plus.homologyFunctor (Sheaves X) q).mapIso e
  exact ⟨fun h => h.of_iso e'.symm, fun h => h.of_iso e'⟩

/-- Compare the two presentations of the stratum in the intersection of their
open chart images. -/
private theorem stratumShriekCohomologyLocality {U X : TopCat.{u}}
    (j : U ⟶ X) (hj : IsOpenEmbedding j) (S : Stratum X) (T : Stratum U)
    (h : Set.range S.inclusion = j '' Set.range T.inclusion)
    (F : BoundedBelow X) (q : ℤ) :
    IsZero ((cohomology S.space q).obj ((S.shriek.obj F).obj)) ↔
      IsZero ((cohomology T.space q).obj ((T.shriek.obj ((boundedBelowInverseImage j).obj F)).obj)) := by
  let e₁ := openInclusion S.ambientOpen
  let e₂ := openInclusion T.ambientOpen ≫ j
  have he₁ : IsOpenEmbedding e₁ := S.ambientOpen.isOpenEmbedding
  have he₂ : IsOpenEmbedding e₂ := hj.comp T.ambientOpen.isOpenEmbedding
  let W : Opens X := ⟨Set.range e₁ ∩ Set.range e₂, he₁.isOpen_range.inter he₂.isOpen_range⟩
  let k := openInclusion W
  have hk : IsOpenEmbedding k := W.isOpenEmbedding
  have hr : Set.range k = Set.range e₁ ∩ Set.range e₂ := Subtype.range_coe
  have hk₁ : Set.range k ⊆ Set.range e₁ := hr ▸ Set.inter_subset_left
  have hk₂ : Set.range k ⊆ Set.range e₂ := hr ▸ Set.inter_subset_right
  let k₁ := liftAlongEmbedding k e₁ he₁.isEmbedding hk₁
  let k₂ := liftAlongEmbedding k e₂ he₂.isEmbedding hk₂
  have hk₁' : k₁ ≫ e₁ = k := liftAlongEmbedding_comp _ _ _ _
  have hk₂' : k₂ ≫ e₂ = k := liftAlongEmbedding_comp _ _ _ _
  have ho₁ : IsOpenEmbedding k₁ := IsOpenEmbedding.of_comp k₁ he₁ (by
    change IsOpenEmbedding (k₁ ≫ e₁)
    rwa [hk₁'])
  have ho₂ : IsOpenEmbedding k₂ := IsOpenEmbedding.of_comp k₂ he₂ (by
    change IsOpenEmbedding (k₂ ≫ e₂)
    rwa [hk₂'])
  let Z : Set (TopCat.of W) := k₁ ⁻¹' S.subset
  have hZ : IsClosed Z := S.closed.preimage k₁.hom.continuous
  let i := closedInclusion Z
  have hZrange : Set.range (i ≫ k) = Set.range S.inclusion := by
    ext x
    constructor
    · rintro ⟨z, rfl⟩
      refine ⟨⟨k₁ z.val, z.property⟩, ?_⟩
      exact congrArg (fun f : TopCat.of W ⟶ X => f z.val) hk₁'
    · rintro ⟨z, rfl⟩
      have hx₁ : S.inclusion z ∈ Set.range e₁ := ⟨z.val, rfl⟩
      have hx₂ : S.inclusion z ∈ Set.range e₂ := by
        have hmem : S.inclusion z ∈ j '' Set.range T.inclusion := h ▸ Set.mem_range_self z
        obtain ⟨y, ⟨w, rfl⟩, hy⟩ := hmem
        exact ⟨w.val, hy⟩
      obtain ⟨w, hw⟩ : S.inclusion z ∈ Set.range k := hr.symm ▸ ⟨hx₁, hx₂⟩
      have hw' : k₁ w = z.val := he₁.injective
        ((congrArg (fun f : TopCat.of W ⟶ X => f w) hk₁').trans hw)
      refine ⟨⟨w, ?_⟩, hw⟩
      change k₁ w ∈ S.subset
      rw [hw']
      exact z.property
  have hTrange : Set.range (T.inclusion ≫ j) = j '' Set.range T.inclusion :=
    Set.range_comp j T.inclusion
  let v₁ := embeddingIsoOfRange S.inclusion (i ≫ k) (stratumEmbedding S)
    (hk.isEmbedding.comp IsEmbedding.subtypeVal) hZrange.symm
  let v₂ := embeddingIsoOfRange (T.inclusion ≫ j) (i ≫ k)
    (hj.isEmbedding.comp (stratumEmbedding T)) (hk.isEmbedding.comp IsEmbedding.subtypeVal)
    (hTrange.trans (hZrange.trans h).symm)
  have hv₁ : v₁.hom ≫ i ≫ k₁ = closedInclusion (X := TopCat.of S.ambientOpen) S.subset := by
    haveI : Mono e₁ := (TopCat.mono_iff_injective _).mpr he₁.injective
    apply (cancel_mono e₁).mp
    simp only [Category.assoc, hk₁']
    exact embeddingIsoOfRange_comp _ _ _ _ _
  have hv₂ : v₂.hom ≫ i ≫ k₂ = closedInclusion (X := TopCat.of T.ambientOpen) T.subset := by
    haveI : Mono e₂ := (TopCat.mono_iff_injective _).mpr he₂.injective
    apply (cancel_mono e₂).mp
    simp only [Category.assoc, hk₂']
    exact embeddingIsoOfRange_comp _ _ _ _ _
  let e : (boundedBelowInverseImage k₁).obj ((boundedBelowInverseImage e₁).obj F) ≅
      (boundedBelowInverseImage k₂).obj
        ((boundedBelowInverseImage (openInclusion T.ambientOpen)).obj
          ((boundedBelowInverseImage j).obj F)) :=
    ((boundedBelowPullbackComposition k₁ e₁).symm.app F) ≪≫
    eqToIso (congrArg (fun l => (boundedBelowInverseImage l).obj F) (hk₁'.trans hk₂'.symm)) ≪≫
    (boundedBelowPullbackComposition k₂ e₂).app F ≪≫
    (boundedBelowInverseImage k₂).mapIso
      ((boundedBelowPullbackComposition (openInclusion T.ambientOpen) j).app F)
  let H := derivedExtraordinaryInverseImage hZ
  let G₁ := H.obj ((boundedBelowInverseImage k₁).obj ((boundedBelowInverseImage e₁).obj F))
  let G₂ := H.obj ((boundedBelowInverseImage k₂).obj
    ((boundedBelowInverseImage (openInclusion T.ambientOpen)).obj ((boundedBelowInverseImage j).obj F)))
  let d₁ := closedShriekOpenIso S.closed hZ k₁ ho₁ v₁ hv₁ ((boundedBelowInverseImage e₁).obj F)
  let d₂ := closedShriekOpenIso T.closed hZ k₂ ho₂ v₂ hv₂
    ((boundedBelowInverseImage (openInclusion T.ambientOpen)).obj ((boundedBelowInverseImage j).obj F))
  exact (cohomologyIsZero_iso_iff d₁ q).trans ((cohomologyIsZero_pullback_iff v₁ G₁ q).trans
    ((cohomologyIsZero_iso_iff (H.mapIso e) q).trans
      ((cohomologyIsZero_pullback_iff v₂ G₂ q).symm.trans (cohomologyIsZero_iso_iff d₂ q).symm)))

open private globalSectionsDirectIso from MathGenome.Internal.RepresentationTheoryDeepening.RepTheorySurvey.Geometric.DerivedLocalSheaves

private def constantPullbackIso {X Y : TopCat.{u}} (f : X ⟶ Y) (V : Coeff.{u}) :
    (inverseImage f).obj (constant Y V) ≅ constant X V :=
  let a := constantSheafAdj (Opens.grothendieckTopology Y) Coeff.{u} (isTerminalTop (α := Opens Y))
  let b := constantSheafAdj (Opens.grothendieckTopology X) Coeff.{u} (isTerminalTop (α := Opens X))
  ((a.comp (inverseDirectAdjunction f)).leftAdjointUniq
    (b.ofNatIsoRight (globalSectionsDirectIso f).symm)).app V

private theorem locallyConstantFiniteRank_of_iso {X : TopCat.{u}} {A B : Sheaves X} (e : A ≅ B)
    (h : LocallyConstantFiniteRank A) : LocallyConstantFiniteRank B := by
  intro x
  obtain ⟨O, hx, V, hV, ⟨c⟩⟩ := h x
  exact ⟨O, hx, V, hV, ⟨(inverseImage (openInclusion O)).mapIso e.symm ≪≫ c⟩⟩

private theorem pullback_locallyConstantFiniteRank {X Y : TopCat.{u}} (f : X ⟶ Y)
    {F : Sheaves Y} (h : LocallyConstantFiniteRank F) :
    LocallyConstantFiniteRank ((inverseImage f).obj F) := by
  intro x
  obtain ⟨O, hx, V, hV, ⟨c⟩⟩ := h (f x)
  let U := (Opens.map f).obj O
  let k : TopCat.of U ⟶ TopCat.of O :=
    TopCat.ofHom ⟨fun z => ⟨f z.val, z.property⟩, (f.hom.continuous.comp continuous_subtype_val).subtype_mk _⟩
  let e : openInclusion U ≫ f = k ≫ openInclusion O := rfl
  refine ⟨U, hx, V, hV, ⟨?_⟩⟩
  exact ((inverseImageComposition (openInclusion U) f).symm.app F) ≪≫
    eqToIso (congrArg (fun l => (inverseImage l).obj F) e) ≪≫
    (inverseImageComposition k (openInclusion O)).app F ≪≫
    (inverseImage k).mapIso c ≪≫ constantPullbackIso k V

private theorem zero_locallyConstantFiniteRank {X : TopCat.{u}} {F : Sheaves X} (h : IsZero F) :
    LocallyConstantFiniteRank F := by
  intro x
  let V : Coeff.{u} := ModuleCat.of ℚ PUnit.{u + 1}
  have hV : Module.Finite ℚ V := inferInstanceAs (Module.Finite ℚ PUnit.{u + 1})
  have hz : IsZero V := ModuleCat.isZero_of_subsingleton _
  let C := constantSheaf (Opens.grothendieckTopology (TopCat.of (⊤ : Opens X))) Coeff.{u}
  haveI : C.IsLeftAdjoint := (constantSheafAdj _ _ (isTerminalTop (α := Opens (TopCat.of (⊤ : Opens X))))).isLeftAdjoint
  have hc : IsZero (C.obj V) := C.map_isZero hz
  exact ⟨⊤, trivial, V, hV, ⟨((inverseImage (openInclusion ⊤)).map_isZero h).iso hc⟩⟩

private def cohomologyOfFactorIso {A U X : TopCat.{u}} {i : A ⟶ X} {m : A ⟶ U}
    (j : U ⟶ X) (h : m ≫ j = i) (G : BoundedBelow X) (F : BoundedBelow U)
    (e : (boundedBelowInverseImage j).obj G ≅ F) (q : ℤ) :
    (inverseImage i).obj ((cohomology X q).obj G.obj) ≅
      (inverseImage m).obj ((cohomology U q).obj F.obj) :=
  eqToIso (congrArg (fun t => (inverseImage t).obj ((cohomology X q).obj G.obj)) h.symm) ≪≫
    (inverseImageComposition m j).app ((cohomology X q).obj G.obj) ≪≫
    (inverseImage m).mapIso
      ((pullbackCohomologyIso j G q).symm ≪≫ (DerivedCategory.Plus.homologyFunctor _ q).mapIso e)

private theorem cohomologyZeroFromOpenClosed {U X : TopCat.{u}} (j : U ⟶ X)
    (F : BoundedBelow X) (q : ℤ)
    (h₁ : IsZero ((cohomology U q).obj ((boundedBelowInverseImage j).obj F).obj))
    (h₂ : IsZero ((cohomology (TopCat.of (boundary j)) q).obj
      ((boundedBelowInverseImage (closedInclusion (boundary j))).obj F).obj)) :
    IsZero ((cohomology X q).obj F.obj) := by
  apply (TopCat.Sheaf.isZero_iff_stalkFunctor_obj_isZero _).mpr
  intro x
  by_cases hx : x ∈ Set.range j
  · obtain ⟨y, rfl⟩ := hx
    exact ((stalk y).map_isZero h₁).of_iso (pullbackStalkIso j F q y).symm
  · let y : boundary j := ⟨x, hx⟩
    change IsZero ((stalk ((closedInclusion (boundary j)) y)).obj ((cohomology X q).obj F.obj))
    exact ((stalk y).map_isZero h₂).of_iso (pullbackStalkIso (closedInclusion (boundary j)) F q y).symm

private theorem attachmentPreviousRange {U X : TopCat.{u}} {j : U ⟶ X}
    {P : Stratification U} {Q : Stratification X} {s : ℕ}
    (H : AttachmentStratification j s P Q) (p : P.Index) :
    Set.range (Q.stratum (H.previousIndex p).val).inclusion =
      Set.range ((P.stratum p).inclusion ≫ j) :=
  (H.previousRange p).trans (Set.range_comp j (P.stratum p).inclusion).symm

private def previousStratumIso {U X : TopCat.{u}} {j : U ⟶ X} (hj : IsOpenEmbedding j)
    {P : Stratification U} {Q : Stratification X} {s : ℕ}
    (H : AttachmentStratification j s P Q) (p : P.Index) :
    (Q.stratum (H.previousIndex p).val).space ≅ (P.stratum p).space :=
  embeddingIsoOfRange _ _ (stratumEmbedding _) (hj.isEmbedding.comp (stratumEmbedding _))
    (attachmentPreviousRange H p)

private theorem closedInclusion_range {X : TopCat.{u}} (Z : Set X) :
    Set.range (closedInclusion Z) = Z :=
  Subtype.range_coe

private def boundaryStratumIso {U X : TopCat.{u}} {j : U ⟶ X}
    {P : Stratification U} {Q : Stratification X} {s : ℕ}
    (H : AttachmentStratification j s P Q) :
    (Q.stratum H.closedIndex).space ≅ TopCat.of (boundary j) :=
  embeddingIsoOfRange (Q.stratum H.closedIndex).inclusion (closedInclusion (boundary j))
    (stratumEmbedding _) IsEmbedding.subtypeVal
    (H.closedRange.trans (closedInclusion_range (boundary j)).symm)

private theorem boundaryStratumIso_comp {U X : TopCat.{u}} {j : U ⟶ X}
    {P : Stratification U} {Q : Stratification X} {s : ℕ}
    (H : AttachmentStratification j s P Q) :
    (boundaryStratumIso H).hom ≫ closedInclusion (boundary j) =
      (Q.stratum H.closedIndex).inclusion :=
  embeddingIsoOfRange_comp (Q.stratum H.closedIndex).inclusion (closedInclusion (boundary j))
    (stratumEmbedding _) IsEmbedding.subtypeVal
    (H.closedRange.trans (closedInclusion_range (boundary j)).symm)

private theorem constructibleFromOpenClosed {U X : TopCat.{u}} (j : U ⟶ X)
    (hj : IsOpenEmbedding j) {P : Stratification U} {Q : Stratification X} {s : ℕ}
    (H : AttachmentStratification j s P Q) (F : BoundedBelow U) (G : BoundedBelow X)
    (e : (boundedBelowInverseImage j).obj G ≅ F) (hF : IsConstructible P F.obj)
    (hG : IsConstructibleOnBoundary j G) : IsConstructible Q G.obj := by
  let I := boundedBelowInverseImage (closedInclusion (boundary j))
  refine ⟨(hF.1.union hG.1).subset ?_, ?_⟩
  · intro q hq
    by_contra h
    have hzF : IsZero ((cohomology U q).obj F.obj) := Classical.not_not.mp
      (fun hz => h (Or.inl hz))
    have hzI : IsZero ((cohomology (TopCat.of (boundary j)) q).obj (I.obj G).obj) :=
      Classical.not_not.mp (fun hz => h (Or.inr hz))
    exact hq (cohomologyZeroFromOpenClosed j G q ((cohomologyIsZero_iso_iff e q).mpr hzF) hzI)
  · intro p q
    by_cases hp : p = H.closedIndex
    · subst p
      let v := boundaryStratumIso H
      let i := closedInclusion (boundary j)
      have hv : v.hom ≫ i = (Q.stratum H.closedIndex).inclusion := boundaryStratumIso_comp H
      let r := cohomologyOfFactorIso i hv G (I.obj G) (Iso.refl _) q
      exact locallyConstantFiniteRank_of_iso r.symm (pullback_locallyConstantFiniteRank _ (hG.2 q))
    · let p' := H.previousIndex.symm ⟨p, hp⟩
      have hp' : (H.previousIndex p').val = p :=
        congrArg Subtype.val (H.previousIndex.apply_symm_apply ⟨p, hp⟩)
      rw [← hp']
      let v := previousStratumIso hj H p'
      let m := (P.stratum p').inclusion
      have hv : (v.hom ≫ m) ≫ j = (Q.stratum (H.previousIndex p').val).inclusion := by
        rw [Category.assoc]
        exact embeddingIsoOfRange_comp _ _ _ _ _
      let r := cohomologyOfFactorIso j hv G F e q ≪≫
        (inverseImageComposition v.hom m).app ((cohomology U q).obj F.obj)
      exact locallyConstantFiniteRank_of_iso r.symm
        (pullback_locallyConstantFiniteRank _ (hF.2 p' q))

private theorem truncationCohomologyIsIso {X : TopCat.{u}} (a q : ℤ) (F : BoundedBelow X)
    (hq : q ≤ a) : IsIso ((DerivedCategory.Plus.homologyFunctor _ q).map
      (truncationTriangle a F).mor₁) := by
  let H := DerivedCategory.Plus.homologyFunctor (Sheaves X) 0
  let T := truncationTriangle a F
  have hT : T ∈ distTriang (BoundedBelow X) := truncationTriangle_distinguished a F
  have h₃₀ := (plusIsGE_iff _ _).mp (truncationTriangle_isGE a F) (q - 1) (by omega)
  have h₃₁ := (plusIsGE_iff _ _).mp (truncationTriangle_isGE a F) q (by omega)
  have hepi : Epi ((H.shift q).map T.mor₁) :=
    (H.homologySequence_epi_shift_map_mor₁_iff T hT q).mpr (h₃₁.eq_of_tgt _ _)
  have hmono : Mono ((H.shift q).map T.mor₁) :=
    (H.homologySequence_mono_shift_map_mor₁_iff T hT (q - 1) q (by omega)).mpr
      (h₃₀.eq_of_src _ _)
  change IsIso ((H.shift q).map T.mor₁)
  exact @isIso_of_mono_of_epi _ _ _ _ _ _ hmono hepi

private theorem constructibleTruncation {X : TopCat.{u}} (P : Stratification X) (a : ℤ)
    (F : BoundedBelow X) (hF : IsConstructible P F.obj) :
    IsConstructible P ((truncLE X a).obj F).obj := by
  let T := truncationTriangle a F
  have hle := (plusIsLE_iff _ _).mp (truncationTriangle_isLE a F)
  refine ⟨hF.1.subset ?_, ?_⟩
  · intro q hq
    have h : q ≤ a := le_of_not_gt (fun h => hq (hle _ h))
    let H := DerivedCategory.Plus.homologyFunctor (Sheaves X) q
    haveI : IsIso (H.map T.mor₁) := truncationCohomologyIsIso a q F h
    exact fun hf => hq (hf.of_iso (asIso (H.map T.mor₁)))
  · intro p q
    by_cases hq : q ≤ a
    · let H := DerivedCategory.Plus.homologyFunctor (Sheaves X) q
      haveI : IsIso (H.map T.mor₁) := truncationCohomologyIsIso a q F hq
      exact locallyConstantFiniteRank_of_iso
        ((inverseImage (P.stratum p).inclusion).mapIso (asIso (H.map T.mor₁)).symm) (hF.2 p q)
    · exact zero_locallyConstantFiniteRank
        ((inverseImage (P.stratum p).inclusion).map_isZero (hle q (lt_of_not_ge hq)))

private theorem boundaryPerverseBounds {U X : TopCat.{u}} {j : U ⟶ X}
    (hj : IsOpenEmbedding j) {P : Stratification U} {Q : Stratification X} {s : ℕ}
    (H : AttachmentStratification j s P Q) (F : BoundedBelow X)
    (hb : IsStrictExtension hj s F) :
    let S := Q.stratum H.closedIndex
    (∀ q : ℤ, -(S.complexDimension : ℤ) < q →
      IsZero ((cohomology S.space q).obj (S.star.obj F.obj))) ∧
    (∀ q : ℤ, q < -(S.complexDimension : ℤ) →
      IsZero ((cohomology S.space q).obj (S.shriek.obj F).obj)) := by
  let S := Q.stratum H.closedIndex
  let v := boundaryStratumIso H
  let i := closedInclusion (boundary j)
  let k := openInclusion S.ambientOpen
  have hv : v.hom ≫ i = S.inclusion := boundaryStratumIso_comp H
  have hd : S.complexDimension = s := H.closedDimension
  constructor
  · intro q hq
    change -(S.complexDimension : ℤ) < q at hq
    rw [hd] at hq
    have h := (plusIsLE_iff _ _).mp hb.1 q (by omega)
    let r := pullbackCohomologyIso S.inclusion F q ≪≫
      cohomologyOfFactorIso i hv F ((boundedBelowInverseImage i).obj F) (Iso.refl _) q
    exact ((inverseImage v.hom).map_isZero h).of_iso r
  · intro q hq
    change q < -(S.complexDimension : ℤ) at hq
    rw [hd] at hq
    have hv' : v.inv ≫ closedInclusion (X := TopCat.of S.ambientOpen) S.subset ≫ k = i := by
      change v.inv ≫ S.inclusion = i
      rw [← hv, Iso.inv_hom_id_assoc]
    let e := closedShriekOpenIso (boundary_isClosed hj) S.closed k S.ambientOpen.isOpenEmbedding
      v.symm hv' F
    exact (cohomologyIsZero_pullback_iff v.symm (S.shriek.obj F) q).mp
      ((cohomologyIsZero_iso_iff e q).mp ((plusIsGE_iff _ _).mp hb.2 q (by omega)))

private theorem previousPerverseBounds {U X : TopCat.{u}} {j : U ⟶ X}
    (hj : IsOpenEmbedding j) {P : Stratification U} {Q : Stratification X} {s : ℕ}
    (H : AttachmentStratification j s P Q) (E : BoundedBelow X) (F : BoundedBelow U)
    (e : (boundedBelowInverseImage j).obj E ≅ F) (hF : IsMiddlePerverse P F.obj)
    (p : P.Index) :
    let S := Q.stratum (H.previousIndex p).val
    (∀ q : ℤ, -(S.complexDimension : ℤ) < q →
      IsZero ((cohomology S.space q).obj (S.star.obj E.obj))) ∧
    (∀ q : ℤ, q < -(S.complexDimension : ℤ) →
      IsZero ((cohomology S.space q).obj (S.shriek.obj E).obj)) := by
  let S := Q.stratum (H.previousIndex p).val
  let T := P.stratum p
  let v := previousStratumIso hj H p
  have hF' := hF.2.choose_spec p
  have hd : S.complexDimension = T.complexDimension := H.previousDimension p
  constructor
  · intro q hq
    change -(S.complexDimension : ℤ) < q at hq
    rw [hd] at hq
    have hv : (v.hom ≫ T.inclusion) ≫ j = S.inclusion := by
      rw [Category.assoc]
      exact embeddingIsoOfRange_comp _ _ _ _ _
    let r := pullbackCohomologyIso S.inclusion E q ≪≫ cohomologyOfFactorIso j hv E F e q ≪≫
      (inverseImageComposition v.hom T.inclusion).app ((cohomology U q).obj F.obj) ≪≫
      (inverseImage v.hom).mapIso (pullbackCohomologyIso T.inclusion F q).symm
    exact ((inverseImage v.hom).map_isZero (hF'.1 q hq)).of_iso r
  · intro q hq
    change q < -(S.complexDimension : ℤ) at hq
    rw [hd] at hq
    apply (stratumShriekCohomologyLocality j hj S T (H.previousRange p) E q).mpr
    exact (cohomologyIsZero_iso_iff (T.shriek.mapIso e) q).mpr (hF'.2 q hq)

theorem attachmentIsMiddleExtension : IntersectionComplex.Expected.AttachmentIsMiddleExtension.{u} := by
  intro U X j hj s P Q H F hF hG
  let a := derivedInverseDirectAdjunctionData j
  let L := boundedBelowInverseImage j
  let G := (derivedDirectImage j).obj F
  let E := (attachment j hj s).obj F
  let n : ℤ := -(s : ℤ) - 1
  obtain ⟨hb, hr⟩ := strictAttachmentOfBound j hj s F (perverseIsLE P F s H.dimension_lt hF)
  haveI : IsIso (a.counit.app F) := openCounitIsIso hj a F
  let eG : L.obj G ≅ F := asIso (a.counit.app F)
  haveI : IsIso (L.map ((attachmentInclusion j hj s).app F) ≫ a.counit.app F) := hr a
  let eE : L.obj E ≅ F := asIso (L.map ((attachmentInclusion j hj s).app F) ≫ a.counit.app F)
  have hGc := constructibleFromOpenClosed j hj H F G eG hF.1 hG
  refine ⟨⟨constructibleTruncation Q n G hGc, E.property, ?_⟩, hb, hr⟩
  intro p
  by_cases h : p = H.closedIndex
  · subst p
    exact boundaryPerverseBounds hj H E hb
  · let q := H.previousIndex.symm ⟨p, h⟩
    have hq : (H.previousIndex q).val = p :=
      congrArg Subtype.val (H.previousIndex.apply_symm_apply ⟨p, h⟩)
    rw [← hq]
    exact previousPerverseBounds hj H E F eE hF q

/-- Transposing an invertible square across the adjunctions gives the open
direct-image comparison when the vertical functors are equivalences. -/
private theorem adjointComparisonIsIso {A B C D : Type*}
    [Category* A] [Category* B] [Category* C] [Category* D]
    (E : B ≌ A) (V : D ≌ C)
    {J : A ⥤ C} {K : B ⥤ D} {S : C ⥤ A} {R : D ⥤ B}
    (α : E.functor ⋙ J ≅ K ⋙ V.functor) (a : J ⊣ S) (b : K ⊣ R) (F : D) :
    IsIso (adjointSquareMap α a b F) := by
  let c := a.homEquiv (E.functor.obj (R.obj F)) (V.functor.obj F)
    (α.hom.app (R.obj F) ≫ V.functor.map (b.counit.app F))
  change IsIso c
  apply isIso_of_yoneda_map_bijective
  intro M
  let N := E.inverse.obj M
  let d : M ≅ E.functor.obj N := E.counitIso.symm.app M
  let p₁ : (M ⟶ E.functor.obj (R.obj F)) ≃ (N ⟶ R.obj F) :=
    (Iso.homCongr d (Iso.refl _)).trans E.fullyFaithfulFunctor.homEquiv.symm
  let p₂ : (N ⟶ R.obj F) ≃ (K.obj N ⟶ F) := (b.homEquiv _ _).symm
  let p₃ : (K.obj N ⟶ F) ≃ (J.obj M ⟶ V.functor.obj F) :=
    V.fullyFaithfulFunctor.homEquiv.trans
      (Iso.homCongr ((J.mapIso d) ≪≫ α.app N).symm (Iso.refl _))
  let p := p₁.trans (p₂.trans (p₃.trans (a.homEquiv _ _)))
  have he (f : M ⟶ E.functor.obj (R.obj F)) :
      E.functor.map (p₁ f) = d.inv ≫ f := by
    change E.functor.map (E.fullyFaithfulFunctor.preimage (d.inv ≫ f ≫ 𝟙 _)) = _
    rw [E.fullyFaithfulFunctor.map_preimage, Category.comp_id]
  have hf (f : M ⟶ E.functor.obj (R.obj F)) : f ≫ c = p f := by
    apply (a.homEquiv _ _).symm.injective
    rw [a.homEquiv_naturality_left_symm]
    change J.map f ≫ (a.homEquiv _ _).symm (a.homEquiv _ _
      (α.hom.app (R.obj F) ≫ V.functor.map (b.counit.app F))) =
      (a.homEquiv _ _).symm (a.homEquiv _ _ (p₃ (p₂ (p₁ f))))
    rw [Equiv.symm_apply_apply, Equiv.symm_apply_apply]
    change _ = (J.map d.hom ≫ α.hom.app N) ≫ V.functor.map ((b.homEquiv _ _).symm (p₁ f)) ≫ 𝟙 _
    rw [Category.comp_id, Adjunction.homEquiv_counit, Functor.map_comp]
    have hn := α.hom.naturality (p₁ f)
    change J.map (E.functor.map (p₁ f)) ≫ α.hom.app (R.obj F) =
      α.hom.app N ≫ V.functor.map (K.map (p₁ f)) at hn
    rw [Category.assoc, ← Category.assoc (α.hom.app N), ← hn, he, Functor.map_comp]
    simp only [Category.assoc, ← Functor.map_comp_assoc, Iso.hom_inv_id_assoc]
  exact (show (fun f => f ≫ c) = p from funext hf) ▸ p.bijective

set_option backward.isDefEq.respectTransparency true in
private theorem directImageComparisonIsIso {U X V Y : TopCat.{u}} {j : U ⟶ X} {k : V ⟶ Y}
    (e : X ≅ Y) (v : U ≅ V) (h : j ≫ e.hom = v.hom ≫ k)
    (a : boundedBelowInverseImage j ⊣ derivedDirectImage j)
    (b : boundedBelowInverseImage k ⊣ derivedDirectImage k) (F : BoundedBelow V) :
    IsIso (directImageComparison h a b F) := by
  let E := pullbackEquivalence e
  let V' := pullbackEquivalence v
  let α : E.functor ⋙ boundedBelowInverseImage j ≅ boundedBelowInverseImage k ⋙ V'.functor :=
    pullbackSquare (j := j) (k := k) (e := e.hom) (v := v.hom) h
  change IsIso (adjointSquareMap α a b F)
  exact adjointComparisonIsIso E V' α a b F

private theorem adjointComparisonNaturality {A B C D : Type*}
    [Category* A] [Category* B] [Category* C] [Category* D]
    {E : B ⥤ A} {V : D ⥤ C}
    {J : A ⥤ C} {K : B ⥤ D} {S : C ⥤ A} {R : D ⥤ B}
    (α : E ⋙ J ≅ K ⋙ V) (a : J ⊣ S) (b : K ⊣ R)
    {F G : D} (f : F ⟶ G) :
    E.map (R.map f) ≫ adjointSquareMap α a b G = adjointSquareMap α a b F ≫ S.map (V.map f) := by
  unfold adjointSquareMap
  apply (a.homEquiv _ _).symm.injective
  rw [a.homEquiv_naturality_left_symm, a.homEquiv_naturality_right_symm]
  simp only [Equiv.symm_apply_apply]
  have hα : J.map (E.map (R.map f)) ≫ α.hom.app (R.obj G) =
      α.hom.app (R.obj F) ≫ V.map (K.map (R.map f)) := α.hom.naturality (R.map f)
  have hb : K.map (R.map f) ≫ b.counit.app G = b.counit.app F ≫ f := b.counit.naturality f
  rw [← Category.assoc, hα, Category.assoc, ← V.map_comp, hb, V.map_comp, Category.assoc]

private theorem directImageComparisonNaturality {U X V Y : TopCat.{u}}
    {j : U ⟶ X} {k : V ⟶ Y} {e : X ⟶ Y} {v : U ⟶ V}
    (h : j ≫ e = v ≫ k) (a : boundedBelowInverseImage j ⊣ derivedDirectImage j)
    (b : boundedBelowInverseImage k ⊣ derivedDirectImage k)
    {F G : BoundedBelow V} (f : F ⟶ G) :
    (boundedBelowInverseImage e).map ((derivedDirectImage k).map f) ≫ directImageComparison h a b G =
      directImageComparison h a b F ≫ (derivedDirectImage j).map ((boundedBelowInverseImage v).map f) :=
  @adjointComparisonNaturality (BoundedBelow X) (BoundedBelow Y) (BoundedBelow U) (BoundedBelow V)
    _ _ _ _ (boundedBelowInverseImage e) (boundedBelowInverseImage v)
    (boundedBelowInverseImage j) (boundedBelowInverseImage k) (derivedDirectImage j) (derivedDirectImage k)
    (pullbackSquare h) a b F G f

private theorem truncationHomBijective {X : TopCat.{u}} (a : ℤ)
    (T : Triangle (BoundedBelow X)) (hT : T ∈ distTriang (BoundedBelow X))
    (h₃ : T.obj₃.IsGE (a + 1)) (A : BoundedBelow X) (hA : A.IsLE a) :
    Function.Bijective (fun f : A ⟶ T.obj₁ => f ≫ T.mor₁) := by
  let t := DerivedCategory.Plus.TStructure.t (C := Sheaves X)
  haveI : t.IsGE T.obj₃ (a + 1) := h₃
  have h₃' : t.IsGE T.invRotate.obj₁ (a + 2) := t.isGE_shift T.obj₃ (a + 1) (-1) (a + 2) (by omega)
  constructor
  · intro f g h
    have h' : (f - g) ≫ T.invRotate.mor₂ = 0 := by
      change (f - g) ≫ T.mor₁ = 0
      change f ≫ T.mor₁ = g ≫ T.mor₁ at h
      rw [Preadditive.sub_comp, h, sub_self]
    obtain ⟨m, hm⟩ := T.invRotate.coyoneda_exact₂ (inv_rot_of_distTriang T hT) _ h'
    exact sub_eq_zero.mp (by rw [hm, t.zero_of_isLE_of_isGE m a (a + 2) (by omega) hA h₃', zero_comp])
  · intro f
    obtain ⟨m, hm⟩ := T.coyoneda_exact₂ hT f (t.zero_of_isLE_of_isGE _ a (a + 1) (by omega) hA h₃)
    exact ⟨m, hm.symm⟩

/-- The ordinary truncation triangle lifted to bounded-below objects. -/
private def truncationTriangleIso₁ {X : TopCat.{u}} {a : ℤ}
    {T S : Triangle (BoundedBelow X)} (hT : T ∈ distTriang (BoundedBelow X))
    (hS : S ∈ distTriang (BoundedBelow X))
    (hT₁ : T.obj₁.IsLE a) (hS₁ : S.obj₁.IsLE a)
    (hT₃ : T.obj₃.IsGE (a + 1)) (hS₃ : S.obj₃.IsGE (a + 1))
    (e : T.obj₂ ≅ S.obj₂) : T.obj₁ ≅ S.obj₁ := by
  let p := truncationHomBijective a S hS hS₃ T.obj₁ hT₁
  let q := truncationHomBijective a T hT hT₃ S.obj₁ hS₁
  let f := Classical.choose (p.2 (T.mor₁ ≫ e.hom))
  let g := Classical.choose (q.2 (S.mor₁ ≫ e.inv))
  have hf : f ≫ S.mor₁ = T.mor₁ ≫ e.hom := Classical.choose_spec (p.2 _)
  have hg : g ≫ T.mor₁ = S.mor₁ ≫ e.inv := Classical.choose_spec (q.2 _)
  refine ⟨f, g, ?_, ?_⟩
  · apply (truncationHomBijective a T hT hT₃ T.obj₁ hT₁).1
    change (f ≫ g) ≫ T.mor₁ = 𝟙 _ ≫ T.mor₁
    rw [Category.assoc, hg, ← Category.assoc, hf]
    simp
  · apply (truncationHomBijective a S hS hS₃ S.obj₁ hS₁).1
    change (g ≫ f) ≫ S.mor₁ = 𝟙 _ ≫ S.mor₁
    rw [Category.assoc, hf, ← Category.assoc, hg]
    simp

private theorem truncationTriangleIso₁_hom_comp {X : TopCat.{u}} {a : ℤ}
    {T S : Triangle (BoundedBelow X)} (hT : T ∈ distTriang (BoundedBelow X))
    (hS : S ∈ distTriang (BoundedBelow X))
    (hT₁ : T.obj₁.IsLE a) (hS₁ : S.obj₁.IsLE a)
    (hT₃ : T.obj₃.IsGE (a + 1)) (hS₃ : S.obj₃.IsGE (a + 1))
    (e : T.obj₂ ≅ S.obj₂) :
    (truncationTriangleIso₁ hT hS hT₁ hS₁ hT₃ hS₃ e).hom ≫ S.mor₁ = T.mor₁ ≫ e.hom :=
  Classical.choose_spec ((truncationHomBijective a S hS hS₃ T.obj₁ hT₁).2 _)

theorem attachmentTransport : IntersectionComplex.Expected.AttachmentTransport.{u} := by
  intro U X V Y j k hj hk e v h s a b
  let n : ℤ := -(s : ℤ) - 1
  let E := boundedBelowInverseImage e.hom
  let V' := boundedBelowInverseImage v.hom
  let J := derivedDirectImage j
  let K := derivedDirectImage k
  let c (F : BoundedBelow V) := directImageComparison h a b F
  haveI (F : BoundedBelow V) : IsIso (c F) := directImageComparisonIsIso e v h a b F
  let T (F : BoundedBelow V) := truncationTriangle n (K.obj F)
  let S (F : BoundedBelow V) := truncationTriangle n (J.obj (V'.obj F))
  have hT (F : BoundedBelow V) : E.mapTriangle.obj (T F) ∈ distTriang (BoundedBelow X) :=
    E.map_distinguished _ (truncationTriangle_distinguished _ _)
  have hS (F : BoundedBelow V) : S F ∈ distTriang (BoundedBelow X) :=
    truncationTriangle_distinguished _ _
  have hTle (F : BoundedBelow V) : (E.mapTriangle.obj (T F)).obj₁.IsLE n :=
    pullbackIsLE _ _ _ (truncationTriangle_isLE _ _)
  have hTge (F : BoundedBelow V) : (E.mapTriangle.obj (T F)).obj₃.IsGE (n + 1) :=
    pullbackIsGE _ _ _ (truncationTriangle_isGE _ _)
  let η (F : BoundedBelow V) :
      (attachment k hk s ⋙ E).obj F ≅ (V' ⋙ attachment j hj s).obj F :=
    truncationTriangleIso₁ (hT F) (hS F) (hTle F) (truncationTriangle_isLE _ _)
      (hTge F) (truncationTriangle_isGE _ _) (asIso (c F))
  have hη (F : BoundedBelow V) :
      (η F).hom ≫ (S F).mor₁ = E.map (T F).mor₁ ≫ c F :=
    truncationTriangleIso₁_hom_comp (hT F) (hS F) (hTle F) (truncationTriangle_isLE _ _)
      (hTge F) (truncationTriangle_isGE _ _) (asIso (c F))
  refine ⟨NatIso.ofComponents η (fun {F G} f => ?_), hη⟩
  apply (truncationHomBijective n (S G) (hS G) (truncationTriangle_isGE _ _) _
    (hTle F)).1
  change (E.map ((attachment k hk s).map f) ≫ (η G).hom) ≫ (S G).mor₁ =
    ((η F).hom ≫ (attachment j hj s).map (V'.map f)) ≫ (S G).mor₁
  have hk' := (attachmentInclusion k hk s).naturality f
  have hj' := (attachmentInclusion j hj s).naturality (V'.map f)
  change (attachment k hk s).map f ≫ (T G).mor₁ = (T F).mor₁ ≫ K.map f at hk'
  change (attachment j hj s).map (V'.map f) ≫ (S G).mor₁ = (S F).mor₁ ≫ J.map (V'.map f) at hj'
  simp only [Category.assoc]
  rw [hη, hj', ← Category.assoc, ← E.map_comp, hk', E.map_comp, Category.assoc, ← Category.assoc (η F).hom, hη,
    Category.assoc, directImageComparisonNaturality h a b f]

private def shiftedConstantPullbackIso {X Y : TopCat.{u}} (e : X ⟶ Y) (d : ℕ) :
    (boundedBelowInverseImage e).obj (shiftedConstant Y d) ≅ shiftedConstant X d := by
  let r : (inverseImage e).obj (rational Y) ≅ rational X := constantPullbackIso e _
  let K := (DerivedCategory.singleFunctor (Sheaves Y) 0).obj (rational Y)
  apply ObjectProperty.isoMk _
  exact ((inverseImage e).mapDerivedCategory.commShiftIso (d : ℤ)).app K ≪≫
    (shiftFunctor (Derived X) (d : ℤ)).mapIso
    (((inverseImage e).mapDerivedCategorySingleFunctor 0).app (rational Y) ≪≫
      (DerivedCategory.singleFunctor (Sheaves X) 0).mapIso r)

theorem complexTransport : IntersectionComplex.Expected.ComplexTransport.{u} := by
  intro X Y s e P Q h
  induction h with
  | top e d => exact ⟨shiftedConstantPullbackIso e.hom d⟩
  | @attach U X V Y d s P Q e v j k hj hk hs _ h ih =>
    obtain ⟨c⟩ := ih
    obtain ⟨τ, _⟩ := attachmentTransport j k hj hk e v h s
      (derivedInverseDirectAdjunctionData j) (derivedInverseDirectAdjunctionData k)
    exact ⟨τ.app (complex Q) ≪≫ (attachment j hj s).mapIso c⟩

end RepTheorySurvey.Geometric.MiddleExtension
