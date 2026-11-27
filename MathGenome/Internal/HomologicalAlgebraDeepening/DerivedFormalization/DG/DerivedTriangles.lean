import MathGenome.Internal.HomologicalAlgebraDeepening.DerivedFormalization.DG.DerivedKProjective
import MathGenome.Internal.HomologicalAlgebraDeepening.DerivedFormalization.DG.HomotopyTriangulation
import MathGenome.Internal.HomologicalAlgebraDeepening.DerivedFormalization.DG.KProjectiveClosure
import MathGenome.Internal.HomologicalAlgebraDeepening.Specs.DerivedFormalization.DG.DerivedTriangles
import Mathlib.Algebra.Homology.HomologySequenceLemmas
import Batteries.Tactic.OpenPrivate

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open HomologicalComplex ComposableArrows

universe u v w t

namespace DerivedFormalization.RightDGModule

open Specs.DerivedFormalization.DG.DerivedTriangles
open Specs.DerivedFormalization.DG.Derived (HomotopyCategoryLaws)
open Specs.DerivedFormalization.DG.DerivedKProjective
  (derivedCategoryInstance kProjectiveObjects)
open Specs.DerivedFormalization.DG.HomComplex (HomotopyEquation)
open private quotientShift_map_heq from MathGenome.Internal.HomologicalAlgebraDeepening.DerivedFormalization.DG.HomotopyPretriangulated
open private homotopyQuotient from MathGenome.Internal.HomologicalAlgebraDeepening.DerivedFormalization.DG.HomotopyShift

noncomputable section

variable {k : Type u} [CommRing k] {A : DGCategory.{u,v,w} k}

private abbrev homologySegment
    {S : ShortComplex (ModuleCochain.{u,v} k)} (hs : S.ShortExact) (i : ℤ) :=
  mk₄ (hs.δ (i - 1) i (by change i - 1 + 1 = i; omega)) (homologyMap S.f i) (homologyMap S.g i)
    (hs.δ i (i + 1) rfl)

private theorem homologySegment_exact
    {S : ShortComplex (ModuleCochain.{u,v} k)} (hs : S.ShortExact) (i : ℤ) :
    (homologySegment hs i).Exact := by
  refine exact_of_δ₀ ?_ (exact_of_δ₀ ?_ ?_)
  · exact (hs.homology_exact₁ (i - 1) i (by change i - 1 + 1 = i; omega)).exact_toComposableArrows
  · exact (hs.homology_exact₂ i).exact_toComposableArrows
  · exact (hs.homology_exact₃ i (i + 1) rfl).exact_toComposableArrows

private theorem shortExact_middle_quasiIso
    {S T : ShortComplex (ModuleCochain.{u,v} k)}
    (hs : S.ShortExact) (ht : T.ShortExact) (φ : S ⟶ T)
    (h₁ : QuasiIso φ.τ₁) (h₃ : QuasiIso φ.τ₃) : QuasiIso φ.τ₂ := by
  rw [quasiIso_iff]
  intro i
  let ψ : homologySegment hs i ⟶ homologySegment ht i :=
    homMk₄ (homologyMap φ.τ₃ (i - 1)) (homologyMap φ.τ₁ i) (homologyMap φ.τ₂ i)
      (homologyMap φ.τ₃ i) (homologyMap φ.τ₁ (i + 1))
      (HomologySequence.δ_naturality φ hs ht _ _ _)
      (naturality' (HomologySequence.mapComposableArrows₂ φ i) 0 1)
      (naturality' (HomologySequence.mapComposableArrows₂ φ i) 1 2)
      (HomologySequence.δ_naturality φ hs ht _ _ _)
  rw [quasiIsoAt_iff_isIso_homologyMap]
  exact Abelian.isIso_of_epi_of_isIso_of_isIso_of_mono
    (homologySegment_exact hs i) (homologySegment_exact ht i) ψ
    (by change Epi (homologyMap φ.τ₃ (i - 1)); infer_instance)
    (by change IsIso (homologyMap φ.τ₁ i); infer_instance)
    (by change IsIso (homologyMap φ.τ₃ i); infer_instance)
    (by change Mono (homologyMap φ.τ₁ (i + 1)); infer_instance)

private theorem coneComparison_quasiIso {M N M' N' : RightDGModule A}
    {f : M ⟶ N} {g : M' ⟶ N'} {a : M ⟶ M'} {b : N ⟶ N'}
    {H : GradedHom M N' (-1)} {c : cone f ⟶ cone g}
    (hc : IsConeComparison a b H c) (ha : IsQuasiIso a) (hb : IsQuasiIso b) :
    IsQuasiIso c := by
  intro o
  let φ : Specs.DerivedFormalization.DG.ShiftCone.objectConeSequence f o ⟶
      Specs.DerivedFormalization.DG.ShiftCone.objectConeSequence g o := {
    τ₁ := b.app o
    τ₂ := c.app o
    τ₃ := (shiftMap 1 a).app o
    comm₁₂ := (congrArg (fun m => RightDGModuleHomModel.app m o) hc.1).symm
    comm₂₃ := congrArg (fun m => RightDGModuleHomModel.app m o) hc.2.1 }
  exact shortExact_middle_quasiIso (coneShortExact f o) (coneShortExact g o) φ
    (hb o) ((CochainComplex.quasiIso_shift_iff (a.app o) 1).mpr (ha o))

/-- The signed comparison from a chosen right-linear homotopy is a quasi-isomorphism. -/
theorem coneSquareComparison_quasiIso : ConeSquareQuasiIso.{u,v,w} := by
  intro k _ A M N M' N' f g a b H hH ha hb
  obtain ⟨c, hi, hp, hm⟩ := coneSquareComparison.{u,v,w} f g a b H hH
  have hc : IsConeComparison a b H c := ⟨hi, hp, hm⟩
  exact ⟨c, hc, coneComparison_quasiIso hc ha hb⟩

/-- A strict lift between K-projective replacements has a quasi-isomorphic cone. -/
theorem replacementConeComparison : ReplacementConeComparison.{u,v,w} := by
  intro k _ A P P' M N p q f hP _ hp hq
  let F := homotopyQuotient A
  obtain ⟨z, hz⟩ := (IsKProjective.homotopyPostcomp_bijective hP (F.map q)
    ((quasiIsomorphisms_homotopyClass q).mpr hq)).surjective (F.map (p ≫ f))
  obtain ⟨g, rfl⟩ := toHomotopyCategory_map_surjective z
  have hgf : homotopyClass (g ≫ q) = homotopyClass (p ≫ f) :=
    (F.map_comp g q).trans hz
  obtain ⟨H, hH⟩ := (homotopyCriterion _ _).mp hgf
  obtain ⟨c, hc, hi⟩ := coneSquareComparison_quasiIso.{u,v,w} g f p q H hH hp hq
  exact ⟨g, H, c, hH, hc, hi⟩

private theorem distinguished_iso_cone_same_endpoints (T : Triangle (K A))
    (hT : T ∈ distTriang (K A)) :
    ∃ f : RightDGModule.Hom T.obj₁ T.obj₂, Nonempty (T ≅ coneTriangle f) := by
  obtain ⟨f, hf⟩ := toHomotopyCategory_map_surjective T.mor₁
  refine ⟨f, ⟨isoTriangleOfIso₁₂ T _ hT (coneTriangle_distinguished f) (.refl _) (.refl _) ?_⟩⟩
  exact (Category.comp_id _).trans (hf.symm.trans (Category.id_comp _).symm)

private theorem isTriangulated_of_strict_cones (P : ObjectProperty (K A))
    (h₀ : P.ContainsZero) (hs : ∀ (M : K A) (n : ℤ), P M → P (shift M n))
    (hc : ∀ {M N : K A} (f : RightDGModule.Hom M N), P M → P N → P (cone f)) :
    P.IsTriangulated := by
  let : P.IsStableUnderShift ℤ := ⟨fun n => ⟨fun M hM => hs M n hM⟩⟩
  let : P.IsTriangulatedClosed₃ := ⟨fun T hT hM hN => by
    obtain ⟨f, ⟨e⟩⟩ := distinguished_iso_cone_same_endpoints T hT
    exact ⟨cone f, hc f hM hN, ⟨Triangle.π₃.mapIso e⟩⟩⟩
  exact { toContainsZero := h₀
          toIsTriangulatedClosed₂ := ObjectProperty.IsTriangulatedClosed₂.of_isTriangulatedClosed₃ }

private abbrev zeroModule (A : DGCategory.{u,v,w} k) := ⊤_ (RightDGModule A)

private theorem zeroModule_identity (A : DGCategory.{u,v,w} k) :
    𝟙 (zeroModule A) = 0 := terminalIsTerminal.hom_ext _ _

private theorem homotopyZero_isZero (A : DGCategory.{u,v,w} k) :
    IsZero ((toHomotopyCategory A).obj (zeroModule A)) := by
  rw [IsZero.iff_id_eq_zero, ← (toHomotopyCategory A).map_id, zeroModule_identity,
    Functor.map_zero]

private theorem zeroModule_KProjective (A : DGCategory.{u,v,w} k) :
    IsKProjective (zeroModule A) := by
  intro N _
  apply acyclic_of_isZero
  rw [IsZero.iff_id_eq_zero]
  apply HomologicalComplex.hom_ext
  intro r
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  change x = 0
  apply GradedHom.ext
  intro a i j e
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro y
  have hy : y = 0 := congrArg (fun f : RightDGModule.Hom (zeroModule A) (zeroModule A) =>
    (f.app a).f i y) (zeroModule_identity A)
  subst y
  simp

private abbrev projectiveObjects (A : DGCategory.{u,v,w} k) : ObjectProperty (K A) :=
  kProjectiveObjects A

private instance kProjectiveObjects_isTriangulated :
    (projectiveObjects A).IsTriangulated :=
  isTriangulated_of_strict_cones _ ⟨⟨_, homotopyZero_isZero A, zeroModule_KProjective A⟩⟩
    (fun _ n hM => IsKProjective.shift n hM)
    (fun f hM hN => IsKProjective.cone f hM hN)

private abbrev acyclicObjects (A : DGCategory.{u,v,w} k) : ObjectProperty (K A) :=
  Acyclic

private theorem zeroModule_acyclic (A : DGCategory.{u,v,w} k) :
    Acyclic (zeroModule A) := by
  intro a
  apply acyclic_of_isZero
  rw [IsZero.iff_id_eq_zero]
  exact congrArg (fun f : RightDGModule.Hom (zeroModule A) (zeroModule A) => f.app a)
    (zeroModule_identity A)

private theorem acyclic_shift {M : RightDGModule A} (hM : Acyclic M) (n : ℤ) :
    Acyclic (shift M n) := by
  intro a i
  exact (exactAt_iff_isZero_homology _ _).2 <|
    ((hM a (i + n)).isZero_homology).of_iso (shiftHomologyIso M n a i)

private theorem acyclic_cone {M N : RightDGModule A} (f : M ⟶ N)
    (hM : Acyclic M) (hN : Acyclic N) : Acyclic (cone f) := by
  apply (quasiIso_iff_cone_acyclic f).mp
  intro a
  rw [quasiIso_iff]
  intro i
  rw [quasiIsoAt_iff_isIso_homologyMap]
  exact (hM a i).isZero_homology.isIso (hN a i).isZero_homology _

private instance acyclicObjects_isTriangulated : (acyclicObjects A).IsTriangulated :=
  isTriangulated_of_strict_cones _ ⟨⟨_, homotopyZero_isZero A, zeroModule_acyclic A⟩⟩
    (fun _ n hM => acyclic_shift hM n) acyclic_cone

private instance acyclicObjects_isClosedUnderIsomorphisms :
    (acyclicObjects A).IsClosedUnderIsomorphisms where
  of_iso {M N} e hM := by
    obtain ⟨f, hf⟩ := toHomotopyCategory_map_surjective e.hom
    obtain ⟨g, hg⟩ := toHomotopyCategory_map_surjective e.inv
    let F := homotopyQuotient A
    change F.map f = e.hom at hf
    change F.map g = e.inv at hg
    have he : homotopyClass (g ≫ f) = homotopyClass (CategoryStruct.id (obj := RightDGModule A) N) := by
      change F.map (g ≫ f) = F.map (CategoryStruct.id (obj := RightDGModule A) N)
      rw [F.map_comp, F.map_id, hg, hf]
      exact e.inv_hom_id
    intro o i
    have hMap := homologyMap_eq_of_homotopyClass_eq he o i
    change homologyMap (g.app o ≫ f.app o) i = homologyMap (𝟙 (N.complex o)) i at hMap
    apply (exactAt_iff_isZero_homology _ _).2
    rw [IsZero.iff_id_eq_zero, ← homologyMap_id, ← hMap, homologyMap_comp]
    rw [(hM o i).isZero_homology.eq_of_tgt (homologyMap (g.app o) i) 0, zero_comp]

private theorem quasiIsomorphisms_eq_trW (A : DGCategory.{u,v,w} k) :
    quasiIsomorphisms A = (acyclicObjects A).trW := by
  ext M N z
  obtain ⟨f, rfl⟩ := homotopyClass_surjective z
  exact (quasiIsomorphisms_homotopyClass f).trans
    ((quasiIso_iff_cone_acyclic f).trans
      ((acyclicObjects A).trW_iff_of_distinguished _ (coneTriangle_distinguished f)).symm)

private instance quasiIsomorphisms_hasLeftCalculusOfFractions :
    (quasiIsomorphisms A).HasLeftCalculusOfFractions := by
  rw [quasiIsomorphisms_eq_trW]
  infer_instance

private instance quasiIsomorphisms_isStableUnderFiniteProducts :
    (quasiIsomorphisms A).IsStableUnderFiniteProducts := by
  rw [quasiIsomorphisms_eq_trW]
  infer_instance

private instance quasiIsomorphisms_isCompatibleWithTriangulation :
    (quasiIsomorphisms A).IsCompatibleWithTriangulation := by
  rw [quasiIsomorphisms_eq_trW]
  infer_instance

set_option maxHeartbeats 800000 in
/-- Use the actual strict comparison to map the signed cone triangles. -/
private def coneTriangleComparison {M N M' N' : RightDGModule A}
    {f : M ⟶ N} {g : M' ⟶ N'} {a : M ⟶ M'} {b : N ⟶ N'}
    {H : GradedHom M N' (-1)} {c : cone f ⟶ cone g}
    (hH : HomotopyEquation (f ≫ b) (a ≫ g) H)
    (hc : IsConeComparison a b H c) : coneTriangle f ⟶ coneTriangle g := by
  let F := homotopyQuotient A
  refine ⟨F.map a, F.map b, F.map c, ?_, ?_, ?_⟩
  · change F.map f ≫ F.map b = F.map a ≫ F.map g
    rw [← F.map_comp, ← F.map_comp]
    exact (homotopyCriterion _ _).mpr ⟨H, hH⟩
  · change F.map (coneInclusion f) ≫ F.map c = F.map b ≫ F.map (coneInclusion g)
    rw [← F.map_comp, ← F.map_comp, hc.1]
  · change (-(F.map (coneProjection f)) ≫ 𝟙 _) ≫
      (homotopyShift (A := A) 1).map (F.map a) =
      F.map c ≫ (-(F.map (coneProjection g)) ≫ 𝟙 _)
    have hp : F.map (coneProjection f) ≫ F.map (shiftMap 1 a) =
        F.map c ≫ F.map (coneProjection g) := by
      rw [← F.map_comp, ← F.map_comp, hc.2.1]
    have hShift : (homotopyShift (A := A) 1).map (F.map a) = F.map (shiftMap 1 a) :=
      @homotopyShift_map k _ A M M' 1 a
    rw [hShift]
    simpa only [eqToHom_refl, Category.comp_id, Preadditive.neg_comp, Preadditive.comp_neg]
      using congrArg Neg.neg hp

private theorem localizedConeComparison {D' : Type*} [Category D'] [HasShift D' ℤ]
    (L : K A ⥤ D') [L.CommShift ℤ] [L.IsLocalization (quasiIsomorphisms A)]
    {M N M' N' : RightDGModule A}
    {f : M ⟶ N} {g : M' ⟶ N'} {a : M ⟶ M'} {b : N ⟶ N'}
    {H : GradedHom M N' (-1)} {c : cone f ⟶ cone g}
    (hH : HomotopyEquation (f ≫ b) (a ≫ g) H) (hc : IsConeComparison a b H c)
    (ha : IsQuasiIso a) (hb : IsQuasiIso b) :
    ∃ e : L.mapTriangle.obj (coneTriangle f) ≅ L.mapTriangle.obj (coneTriangle g),
      e.hom.hom₁ = L.map (homotopyClass a) ∧
      e.hom.hom₂ = L.map (homotopyClass b) ∧
      e.hom.hom₃ = L.map (homotopyClass c) := by
  let φ := L.mapTriangle.map (coneTriangleComparison hH hc)
  have map_isIso {U V : RightDGModule A} (p : U ⟶ V) (hp : IsQuasiIso p) :
      IsIso (L.map (homotopyClass p)) :=
    Localization.inverts L (quasiIsomorphisms A) _
      ((quasiIsomorphisms_homotopyClass p).mpr hp)
  let : IsIso φ := Triangle.isIso_of_isIsos φ
    (map_isIso _ ha) (map_isIso _ hb) (map_isIso _ (coneComparison_quasiIso hc ha hb))
  exact ⟨asIso φ, rfl, rfl, rfl⟩

private theorem derived_distinguished_iff_projective_cone
    {A : DGCategory.{u,max v w,w} k}
    {D' : Type*} [Category D'] [HasShift D' ℤ] [Preadditive D'] [HasZeroObject D']
    [∀ n : ℤ, (shiftFunctor D' n).Additive] [Pretriangulated D']
    (L : K A ⥤ D') [L.CommShift ℤ] [L.IsLocalization (quasiIsomorphisms A)]
    [L.IsTriangulated] [L.mapArrow.EssSurj] (T : Triangle D') :
    T ∈ distTriang D' ↔
      ∃ (M N : RightDGModule A) (_ : IsKProjective M) (_ : IsKProjective N) (f : M ⟶ N),
        Nonempty (T ≅ L.mapTriangle.obj (coneTriangle f)) := by
  constructor
  · intro hT
    obtain ⟨U, e, hU⟩ := (L.distTriang_iff T).mp hT
    obtain ⟨f, ⟨ef⟩⟩ := distinguished_iso_cone_same_endpoints U hU
    obtain ⟨P, p, hp, _, hpi⟩ := unboundedSemiFreeResolutionInUniverse.{u,v,w} k A U.obj₁
    obtain ⟨P', q, hq, _, hqi⟩ := unboundedSemiFreeResolutionInUniverse.{u,v,w} k A U.obj₂
    have hP := IsSemiFree.isKProjective hp
    have hP' := IsSemiFree.isKProjective hq
    obtain ⟨g, H, c, hH, hc, _⟩ := replacementConeComparison p q f hP hP' hpi hqi
    obtain ⟨e', _, _, _⟩ := localizedConeComparison L hH hc hpi hqi
    exact ⟨P, P', hP, hP', g, ⟨e ≪≫ L.mapTriangle.mapIso ef ≪≫ e'.symm⟩⟩
  · rintro ⟨M, N, _, _, f, ⟨e⟩⟩
    exact isomorphic_distinguished _ (L.map_distinguished _ (coneTriangle_distinguished f)) _ e

private theorem specConeTriangle_eq (h : HomotopyCategoryLaws A)
    {M N : RightDGModule A} (f : M ⟶ N) :
    (Specs.DerivedFormalization.DG.DerivedTriangles.coneTriangle h homotopyHasShift rfl f :
        Triangle (K A)) = coneTriangle f := by
  rfl

set_option maxHeartbeats 800000 in
/-- The full K-projective homotopy subcategory inherits its triangulation,
and its restriction of localization is a triangulated equivalence. -/
theorem nativeDerivedTriangulation : NativeTriangulation.{u,v,w} := by
  intro k _ A h
  let W := quasiIsomorphisms A
  let L := W.Q
  have : L.mapArrow.EssSurj := Localization.essSurj_mapArrow L W
  let S : HasShift W.Localization ℤ := inferInstance
  let I : L.CommShift ℤ := inferInstance
  let AD : Preadditive W.Localization := inferInstance
  let ZD : HasZeroObject W.Localization := inferInstance
  let LD (n : ℤ) : (shiftFunctor W.Localization n).Additive := inferInstance
  let TD : Pretriangulated W.Localization := inferInstance
  have hL : L.IsTriangulated :=
    Triangulated.Localization.isTriangulated_functor L W
  have hR : ((projectiveObjects A).ι ⋙ L).IsTriangulated := inferInstance
  refine ⟨homotopyHasShift, homotopyPreadditive, homotopyHasZeroObject,
    homotopyShiftAdditive, fun _ _ => rfl, homotopyPretriangulated, homotopyIsTriangulated,
    ?_, ?_, kProjectiveObjects_isTriangulated, ?_, S, AD, ZD, LD, I, TD, ?_, hL,
    kProjectiveLocalization_isEquivalence A h, hR,
    ?_, ?_, ?_⟩
  · intro M N n f
    change HEq ((shiftFunctor (K A) n).map ((homotopyQuotient A).map f))
      ((homotopyQuotient A).map (shiftMap n f))
    exact @quotientShift_map_heq k _ A M N n f
  · intro T
    simpa only [specConeTriangle_eq] using distinguished_iff_cone_triangle T
  · exact (inferInstance : IsTriangulated (projectiveObjects A).FullSubcategory)
  · exact (inferInstance : IsTriangulated W.Localization)
  · intro T
    change Triangle W.Localization at T
    change T ∈ distTriang W.Localization ↔
      ∃ (M N : RightDGModule A) (_ : IsKProjective M) (_ : IsKProjective N) (f : M ⟶ N),
        Nonempty (T ≅ L.mapTriangle.obj
          (Specs.DerivedFormalization.DG.DerivedTriangles.coneTriangle h homotopyHasShift rfl f))
    simpa only [specConeTriangle_eq] using derived_distinguished_iff_projective_cone L T
  · intro M N f
    change L.mapTriangle.obj
      (Specs.DerivedFormalization.DG.DerivedTriangles.coneTriangle h homotopyHasShift rfl f) ∈
        distTriang W.Localization
    simpa only [specConeTriangle_eq] using L.map_distinguished _ (coneTriangle_distinguished f)
  · intro M N M' N' f g a b H c hH hc ha hb
    change ∃ e : L.mapTriangle.obj (coneTriangle f) ≅ L.mapTriangle.obj (coneTriangle g),
      e.hom.hom₁ = L.map (homotopyClass a) ∧
      e.hom.hom₂ = L.map (homotopyClass b) ∧
      e.hom.hom₃ = L.map (homotopyClass c)
    exact localizedConeComparison L hH hc ha hb

/-- The same triangulation in the common adequate localization of the original
dg category, with native K-projective replacements at that bound. -/
theorem ambientDerivedTriangulation : AmbientTriangulation.{u,v,w,t} := by
  intro k _ A h
  exact nativeDerivedTriangulation.{u,max v t,w} _ h

private def triangleThirdIso {C : Type*} [Category C] [HasShift C ℤ]
    {X Y Z Z' : C} (f : X ⟶ Y) (j : Y ⟶ Z) (j' : Y ⟶ Z')
    (p : Z ⟶ (shiftFunctor C (1 : ℤ)).obj X)
    (p' : Z' ⟶ (shiftFunctor C (1 : ℤ)).obj X) (e : Z ≅ Z')
    (hj : j ≫ e.hom = j') (hp : p = e.hom ≫ p') :
    Triangle.mk f j p ≅ Triangle.mk f j' p' :=
  Triangle.isoMk _ _ (Iso.refl _) (Iso.refl _) e
    (by simp) (by simpa using hj) (by simpa using hp)

set_option maxHeartbeats 800000 in
/-- Localizing the strict coordinate isomorphism identifies the lifted original
cone with the cone of the lifted map, with its signed third arrow. -/
theorem liftedConeTriangleComparison : LiftedConeTriangleComparison.{u,v,w,t} := by
  intro k _ A B F h K' D' L SK hS SD qS M N f
  let : Category K' := Specs.DerivedFormalization.DG.Derived.homotopyCategory B h
  let : Category D' := derivedCategoryInstance B h
  let : HasShift K' ℤ := SK
  let : HasShift (K B) ℤ := SK
  let : HasShift D' ℤ := SD
  let : L.CommShift ℤ := qS
  let U := homotopyQuotient B
  obtain ⟨s, _, c, hcoord, hmaps, _⟩ :=
    DG.CoefficientLift.coneComparison.{u,v,w,max w t} (A := A)
  have hi : F.map (coneInclusion f) ≫ (c f).hom = coneInclusion (F.map f) := (hmaps f).1
  have hp : F.map (coneProjection f) ≫ (s M).hom = (c f).hom ≫ coneProjection (F.map f) :=
    (hmaps f).2
  let j := U.map (F.map (coneInclusion f))
  let j' := U.map (coneInclusion (F.map f))
  let p := U.map (F.map (coneProjection f) ≫ (s M).hom)
  let p' := U.map (coneProjection (F.map f))
  let e := U.mapIso (c f)
  let eqShift := eqToHom (hS (F.obj M) 1).symm
  have hj : j ≫ e.hom = j' := (U.map_comp _ _).symm.trans (congrArg U.map hi)
  have hs : p = e.hom ≫ p' := (congrArg U.map hp).trans (U.map_comp _ _)
  have hs' : -(p ≫ eqShift) = e.hom ≫ (-(p' ≫ eqShift)) := by
    rw [hs, Preadditive.comp_neg, Category.assoc]
  let e' := triangleThirdIso (U.map (F.map f)) j j' (-(p ≫ eqShift)) (-(p' ≫ eqShift)) e hj hs'
  refine ⟨s M, c f, hcoord f, hi, hp, L.mapTriangle.mapIso e', ?_, ?_, rfl⟩
  · exact L.map_id _
  · exact L.map_id _

end

end DerivedFormalization.RightDGModule
