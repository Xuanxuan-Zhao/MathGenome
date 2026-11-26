import Specs.LinearAlgebraicGroups.Solvable.UnipotentRadical
import LinearAlgebraicGroups.Reductive.GeometricRadicals
import LinearAlgebraicGroups.Affine.SchemeImageQuotient
import LinearAlgebraicGroups.Solvable.LieKolchin
import LinearAlgebraicGroups.Solvable.SmoothDiagonalKernel
import Batteries.Tactic.OpenPrivate
import Mathlib.AlgebraicGeometry.Morphisms.FlatMono
import Mathlib.RingTheory.KrullDimension.Field
import Mathlib.RingTheory.KrullDimension.Polynomial
import Mathlib.CategoryTheory.Limits.EpiMono

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open scoped TensorProduct
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj CategoryTheory.GrpObj

universe u

namespace LinearAlgebraicGroups.SolvableRadical

open _root_.LinearAlgebraicGroups.Specs (IsSchemeKernel IsImageFactorization)
open Specs.SolvableRadical
open Specs.GeometricRadicals (IsTorus IsSmoothConnectedNormal IsUnipotentRadical)
open Specs.SchemeDerivedGroup (IsSolvable IsSubgroupOf)
open Specs.Unipotent (IsUnipotent closedSubgroupAlgebraicGroup Index IsFppfGroupQuotient
  baseChangedAlgebraicGroup)
open Specs.Triangularization (upperTriangular upperTriangularPoints)
open Specs.StandardGroups (generalLinearPoints multiplicativePowerPoints)
open Specs.SmoothDiagonalKernel (IsUpperTriangular)

noncomputable section

variable {k : Type u} [Field k]

set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1600000
set_option linter.style.haveILetI false

open private groupPresentation quotientRepresentsImage
  from LinearAlgebraicGroups.Affine.SchemeImageQuotient
open private hom_ext_of_points from LinearAlgebraicGroups.Affine.GroupSchemes
open private baseChangeMapPullback baseChangeKernelSquare
  from LinearAlgebraicGroups.Affine.Components
open private geometricallyConnected_of_connected geometricallyIrreducible_of_connected
  smooth_geometricallyIrreducible_tensor geometry_of_smooth_geometricallyIrreducible
  from LinearAlgebraicGroups.Solvable.WordDomainGeometry
open private SmoothDiagonalKernel.liftToSchemeKernel
  from LinearAlgebraicGroups.Solvable.SmoothDiagonalKernel

theorem solvableUnipotentRadicalUnique : SolvableUnipotentRadicalUnique.{u} := by
  intro k _ G U V hU hV
  exact GeometricRadicals.radicalUnique G IsUnipotent
    ⟨hU.1, hU.2.1, fun H _ hH ↦ hU.2.2 H hH⟩
    ⟨hV.1, hV.2.1, fun H _ hH ↦ hV.2.2 H hH⟩

private theorem quotient_of_flat_surjective {G T : AffineAlgebraicGroup k}
    {q : G.val ⟶ T.val} {U : ClosedSubgroup G.val} (hker : IsSchemeKernel q U)
    (hf : Flat q.hom.hom.left) (hs : Surjective q.hom.hom.left)
    (hfp : LocallyOfFinitePresentation q.hom.hom.left) :
    IsFppfGroupQuotient (G := G) (Q := T) U q := by
  have := T.property.1
  have := G.property.1
  refine ⟨hker, hf, hs, hfp, quotientRepresentsImage
    (i := 𝟙 T.val) (p := q) ?_ hker⟩
  exact ⟨Category.comp_id _, hf, hs, hfp, inferInstance,
    inferInstanceAs (IsClosedImmersion (𝟙 T.val.X.left))⟩

private theorem kernel_of_mono_factor {G D T : GroupScheme k}
    {p : G ⟶ D} {i : D ⟶ T} {U : ClosedSubgroup G}
    (hi : IsClosedImmersion i.hom.hom.left) (hU : IsSchemeKernel (p ≫ i) U) :
    IsSchemeKernel p U := by
  letI : Mono i.hom.hom := Over.mono_of_mono_left _
  have hunit : η[D.X] ≫ i.hom.hom = η[T.X] := IsMonHom.one_hom _
  have ht : IsPullback (𝟙 (𝟙_ (SchemeOver k))) η[D.X] η[T.X] i.hom.hom :=
    IsPullback.of_horiz_isIso_mono ⟨(Category.id_comp _).trans hunit.symm⟩
  have hfull : IsPullback U.inclusion.hom.hom (toUnit U.group.X ≫ 𝟙 _)
      (p.hom.hom ≫ i.hom.hom) η[T.X] := by
    rw [Category.comp_id]
    exact hU
  have hsq : U.inclusion.hom.hom ≫ p.hom.hom = toUnit U.group.X ≫ η[D.X] := by
    apply (cancel_mono i.hom.hom).mp
    have h := hU.w
    change U.inclusion.hom.hom ≫ (p.hom.hom ≫ i.hom.hom) =
      toUnit U.group.X ≫ η[T.X] at h
    simpa only [Category.assoc, hunit] using h
  exact hfull.of_bot hsq ht.flip

private def triangularInclusion (k : Type u) [Field k] (n : ℕ) :
    upperTriangularPoints k n ⟶ generalLinearPoints k (Index.{u} n) where
  app R := GrpCat.ofHom (upperTriangular (Index.{u} n) R).subtype
  naturality _ _ _ := rfl

/-- Injectivity on affine test schemes forces the faithfully flat image factor to
be an isomorphism. The universal pair lives in an affine fibre product. -/
private theorem closed_of_injective_on_points {B H : AffineAlgebraicGroup k}
    (i : B.val ⟶ H.val)
    (hi : ∀ R : TestAlgebra k, Function.Injective (((groupPointsFunctor k).map i).app R)) :
    IsClosedImmersion i.hom.hom.left := by
  obtain ⟨I, p, j, hp, _, _⟩ := schemeImageFactorization B H i
  have := B.property.1
  have := I.property.1
  have := hp.2.1
  have := hp.2.2.1
  have := hp.2.2.2.2.2
  let X := pullback p.hom.hom p.hom.hom
  have hX : IsAffine X.left := by
    let F := Over.forget (Spec (CommRingCat.of k))
    let e := PreservesPullback.iso F p.hom.hom p.hom.hom
    have : IsAffineHom (F.map p.hom.hom) := hp.2.2.2.2.1
    have : IsAffine ((F.obj B.val.X)) := B.property.1
    have : IsAffine (pullback (F.map p.hom.hom) (F.map p.hom.hom)) :=
      isAffine_of_isAffineHom (pullback.fst _ _)
    exact isAffine_of_isAffineHom e.hom
  have hfst : pullback.fst p.hom.hom p.hom.hom = pullback.snd p.hom.hom p.hom.hom := by
    apply hom_ext_of_points hX
    intro R x
    apply hi R
    change (x ≫ pullback.fst _ _) ≫ i.hom.hom = (x ≫ pullback.snd _ _) ≫ i.hom.hom
    rw [← hp.1]
    change (x ≫ pullback.fst _ _) ≫ p.hom.hom ≫ j.hom.hom =
      (x ≫ pullback.snd _ _) ≫ p.hom.hom ≫ j.hom.hom
    simp only [Category.assoc, pullback.condition_assoc]
  have hm : Mono p.hom.hom :=
    (mono_iff_fst_eq_snd (IsPullback.of_hasPullback p.hom.hom p.hom.hom).isLimit).mpr hfst
  have hml : Mono p.hom.hom.left := (Over.forget _).map_mono _
  have hpi := Flat.isIso_of_surjective_of_mono p.hom.hom.left
  rw [← hp.1]
  exact IsClosedImmersion.comp p.hom.hom.left j.hom.hom.left

private theorem triangularMatrixEmbedding (G : AffineAlgebraicGroup k)
    (h : Specs.Triangularization.EmbedsUpperTriangular G) :
    ∃ (n : ℕ) (H : AffineAlgebraicGroup k) (j : G.val ⟶ H.val)
        (e : (groupPointsFunctor k).obj H.val ≅ generalLinearPoints k (Index.{u} n)),
      IsClosedImmersion j.hom.hom.left ∧ IsUpperTriangular j e := by
  classical
  obtain ⟨n, B, ⟨b⟩, f, hf⟩ := h
  let H := StandardGroups.generalLinearGroup k (Index.{u} n)
  let e := StandardGroups.generalLinearGroupPointsIso k (Index.{u} n)
  let α := b.hom ≫ triangularInclusion k n ≫ e.inv
  let i := (AffineAlgebraicGroup.groupHomEquiv B H).symm α
  have hi : (groupPointsFunctor k).map i = α :=
    (AffineAlgebraicGroup.groupHomEquiv B H).apply_symm_apply α
  have hc : IsClosedImmersion i.hom.hom.left := by
    apply closed_of_injective_on_points i
    intro R x y hxy
    rw [hi] at hxy
    apply (b.app R).groupIsoToMulEquiv.injective
    apply Subtype.ext
    exact (e.app R).groupIsoToMulEquiv.symm.injective hxy
  refine ⟨n, H, f ≫ i, e, ?_, ?_⟩
  · have := hf
    change IsClosedImmersion (f.hom.hom.left ≫ i.hom.hom.left)
    infer_instance
  · intro R x
    let y := ((groupPointsFunctor k).map f).app R x
    change (e.hom.app R (((groupPointsFunctor k).map (f ≫ i)).app R x)).val.IsUpperTriangular
    rw [(groupPointsFunctor k).map_comp, NatTrans.comp_app, GrpCat.comp_apply, hi]
    change (e.hom.app R (e.inv.app R ((b.hom.app R y).val))).val.IsUpperTriangular
    rw [show e.hom.app R (e.inv.app R ((b.hom.app R y).val)) = (b.hom.app R y).val from
      (e.app R).groupIsoToMulEquiv.apply_symm_apply _]
    exact (b.hom.app R y).property

private theorem geometricRadicalQuotient [IsAlgClosed k] (G : AffineAlgebraicGroup k)
    (hs : Smooth G.val.X.hom) (hc : ConnectedSpace G.val.X.left) (hv : IsSolvable G.val) :
    ∃ (U : ClosedSubgroup G.val) (T : AffineAlgebraicGroup k) (q : G.val ⟶ T.val),
      IsSolvableUnipotentRadical G U ∧ IsTorus T.val ∧ IsFppfGroupQuotient U q := by
  obtain ⟨A, _, ⟨a⟩⟩ := groupPresentation G
  have hflag := LieKolchin.invariantFullFlag G A a hs hc hv
  have htri := (Triangularization.triangularization G A a).2.1.mp hflag
  obtain ⟨n, H, j, e, hj, htop⟩ := triangularMatrixEmbedding G htri
  let P := StandardGroups.multiplicativePowerGroup k (Index.{u} n)
  let t := StandardGroups.multiplicativePowerGroupPointsIso k (Index.{u} n)
  obtain ⟨d, _, T, q, i, U, hi, _, hker, ⟨C, ⟨c⟩, hC⟩, hus, huc, hun, huu, hmax⟩ :=
    SmoothDiagonalKernel.smoothDiagonalKernel n G H P j e t hj htop hs hc
  have hk : IsSchemeKernel q U := kernel_of_mono_factor hi.2.2.2.2.2 (hi.1.symm ▸ hker)
  refine ⟨U, T, q, ⟨⟨hus, huc, hun⟩, huu, hmax⟩, ?_,
    quotient_of_flat_surjective hk hi.2.1 hi.2.2.1 hi.2.2.2.1⟩
  obtain ⟨E, _, _, _, r, ⟨d⟩⟩ := GeometricRadicals.torusCoordinateComparison C |>.mpr hC
  exact ⟨E, inferInstance, inferInstance, inferInstance, r,
    ⟨(groupBaseChange k E).mapIso c.symm ≪≫ d⟩⟩

open Specs.FiniteWordClosure (power wordDomain evaluate)
open private FiniteWordClosure.affine_tensor FiniteWordClosure.affine_power
  from LinearAlgebraicGroups.Solvable.FiniteWordClosure
open private SchemeDerivedGroup.power_geometry SchemeDerivedGroup.evaluate_mem
  from LinearAlgebraicGroups.Solvable.SchemeDerivedGroup
open private GeometricRadicals.productMap GeometricRadicals.comp_productMap
  GeometricRadicals.productMap_conjugationStable GeometricRadicals.productMap_mem_sup
  GeometricRadicals.product_sections_of_mem_sup GeometricRadicals.unipotent_product
  GeometricRadicals.identity_smoothConnectedNormal GeometricRadicals.identity_unipotent
  GeometricRadicals.isIso_of_schemeIso GeometricRadicals.factor_closed
  from LinearAlgebraicGroups.Reductive.GeometricRadicals
open private isMonHom_of_comp_closed from LinearAlgebraicGroups.Affine.SchemeImageQuotient
open private smooth_of_smooth_after_fieldExtension isReduced_of_smooth_over_field from LinearAlgebraicGroups.Affine.SmoothnessCriteria

private theorem smooth_of_dominant_smooth {X : SchemeOver k} {N : GroupScheme k}
    (p : X ⟶ N.X) [QuasiCompact p.left] [IsSchemeTheoreticallyDominant p.left]
    [Smooth X.hom] [LocallyOfFiniteType N.X.hom] :
    Smooth N.X.hom := by
  let L := AlgebraicClosure k
  let F := baseChange k L
  let f := fieldSpecMap k L
  have : Flat (pullback.fst N.X.hom f) := inferInstance
  have hd : IsSchemeTheoreticallyDominant (F.map p).left :=
    IsSchemeTheoreticallyDominant.of_isPullback (baseChangeMapPullback p).flip
  have : Smooth (F.obj X).hom := inferInstanceAs (Smooth (pullback.snd X.hom f))
  have : LocallyOfFiniteType (F.obj N.X).hom :=
    inferInstanceAs (LocallyOfFiniteType (pullback.snd N.X.hom f))
  have hqc : QuasiCompact (F.map p).left :=
    MorphismProperty.of_isPullback (baseChangeMapPullback p).flip inferInstance
  have : IsReduced (F.obj X).left := isReduced_of_smooth_over_field (F.obj X).hom
  have hr : IsReduced (F.obj N.X).left := IsSchemeTheoreticallyDominant.isReduced (F.map p).left
  have hs : Smooth ((groupBaseChange k L).obj N).X.hom :=
    smoothOfReducedOverPerfectField L _ hr
  exact smooth_of_smooth_after_fieldExtension N.X.hom hs

/-- The scheme image of the product of normal smooth connected subgroups
is again a normal smooth connected subgroup, over any field. -/
private theorem smoothNormalProduct (G : AffineAlgebraicGroup k) (H K : ClosedSubgroup G.val)
    (hH : IsSmoothConnectedNormal H) (hK : IsSmoothConnectedNormal K) :
    ∃ N : ClosedSubgroup G.val, ∃ j : H.group ⟶ N.group, ∃ l : K.group ⟶ N.group,
      IsSmoothConnectedNormal N ∧ j ≫ N.inclusion = H.inclusion ∧ l ≫ N.inclusion = K.inclusion ∧
      IsSchemeTheoreticallyDominant
        (((fst H.group.X K.group.X) ≫ j.hom.hom) *
          ((snd H.group.X K.group.X) ≫ l.hom.hom)).left := by
  let A := closedSubgroupAlgebraicGroup H
  let B := closedSubgroupAlgebraicGroup K
  let X := H.group.X ⊗ K.group.X
  let f := GeometricRadicals.productMap H K
  have : IsAffine H.group.X.left := A.property.1
  have : IsAffine K.group.X.left := B.property.1
  have : IsAffine X.left := FiniteWordClosure.affine_tensor (A := H.group.X) (B := K.group.X)
  have : Smooth H.group.X.hom := hH.1
  have : Smooth K.group.X.hom := hK.1
  have : ConnectedSpace A.val.X.left := hH.2.1
  have : ConnectedSpace B.val.X.left := hK.2.1
  have : GeometricallyIrreducible H.group.X.hom := geometricallyIrreducible_of_connected A
  have : GeometricallyIrreducible K.group.X.hom := geometricallyIrreducible_of_connected B
  obtain ⟨hXs, hXi⟩ := smooth_geometricallyIrreducible_tensor H.group.X K.group.X
  have hpow (m : ℕ) : IsIntegral (power X m).left := by
    obtain ⟨_, _⟩ := SchemeDerivedGroup.power_geometry X m
    exact (geometry_of_smooth_geometricallyIrreducible (power X m)).2.2
  let x₀ : 𝟙_ (SchemeOver k) ⟶ X := lift 1 1
  have hx₀ : x₀ ≫ f = 1 := by
    change lift 1 1 ≫ GeometricRadicals.productMap H K = _
    rw [GeometricRadicals.comp_productMap, map_one, map_one, one_mul]
  obtain ⟨N, n, w, _, hn, hd, ⟨fN, hfN⟩, _, hw⟩ :=
    FiniteWordClosure.existsFiniteWordClosure G X f x₀ inferInstance inferInstance inferInstance
      hx₀ hpow (GeometricRadicals.productMap_conjugationStable hH.2.2 hK.2.2)
  have : IsAffine N.group.X.left := (closedSubgroupAlgebraicGroup N).property.1
  have : LocallyOfFiniteType N.group.X.hom := (closedSubgroupAlgebraicGroup N).property.2.1
  have : IsIntegral (wordDomain X n).left := hpow (2 * n)
  have : IsAffine (wordDomain X n).left := FiniteWordClosure.affine_power (2 * n)
  have : Smooth (wordDomain X n).hom := (SchemeDerivedGroup.power_geometry X (2 * n)).1
  have hNs := smooth_of_dominant_smooth (N := N.group) w
  have hNc : ConnectedSpace N.group.X.left :=
    { toPreconnectedSpace := w.left.denseRange.preconnectedSpace w.left.continuous
      toNonempty := ⟨w.left (Classical.choice (inferInstance : Nonempty (wordDomain X n).left))⟩ }
  have := N.isClosedImmersion
  have : Mono N.inclusion.hom.hom := Over.mono_of_mono_left _
  let j₀ := lift (𝟙 H.group.X) (1 : H.group.X ⟶ K.group.X) ≫ fN
  let l₀ := lift (1 : K.group.X ⟶ H.group.X) (𝟙 K.group.X) ≫ fN
  have hj₀ : j₀ ≫ N.inclusion.hom.hom = H.inclusion.hom.hom := by
    rw [Category.assoc, hfN, GeometricRadicals.comp_productMap, map_one, mul_one]
    change 𝟙 H.group.X ≫ H.inclusion.hom.hom = _
    exact Category.id_comp _
  have hl₀ : l₀ ≫ N.inclusion.hom.hom = K.inclusion.hom.hom := by
    rw [Category.assoc, hfN, GeometricRadicals.comp_productMap, map_one, one_mul]
    change 𝟙 K.group.X ≫ K.inclusion.hom.hom = _
    exact Category.id_comp _
  have := isMonHom_of_comp_closed j₀ H.inclusion N.inclusion hj₀
  have := isMonHom_of_comp_closed l₀ K.inclusion N.inclusion hl₀
  let j := Grp.homMk j₀
  let l := Grp.homMk l₀
  refine ⟨N, j, l, ⟨hNs, hNc, hn⟩, Grp.hom_ext _ _ hj₀, Grp.hom_ext _ _ hl₀, ?_⟩
  have hf : ((fst H.group.X K.group.X ≫ j₀) * (snd H.group.X K.group.X ≫ l₀)) = fN := by
    apply (cancel_mono N.inclusion.hom.hom).mp
    rw [MonObj.mul_comp, Category.assoc (fst _ _) j₀, Category.assoc (snd _ _) l₀, hj₀, hl₀, hfN]
    rfl
  change IsSchemeTheoreticallyDominant
    (((fst H.group.X K.group.X ≫ j₀) * (snd H.group.X K.group.X ≫ l₀))).left
  rw [hf]
  let T := wordDomain X n
  let S := Specs.SubgroupSections H T ⊔ Specs.SubgroupSections K T
  have hword : evaluate f n (𝟙 T) ∈ S :=
    SchemeDerivedGroup.evaluate_mem f S (GeometricRadicals.productMap_mem_sup H K) n (𝟙 T)
  obtain ⟨x, y, hxy⟩ := GeometricRadicals.product_sections_of_mem_sup hH.2.2 hword
  have hw' : w = lift x y ≫ fN := by
    apply (cancel_mono N.inclusion.hom.hom).mp
    rw [Category.assoc, hfN, GeometricRadicals.comp_productMap]
    have he : w ≫ N.inclusion.hom.hom = evaluate f n (𝟙 T) := by
      simpa only [Category.id_comp] using hw T (𝟙 T)
    exact he.trans hxy.symm
  have hdom : IsSchemeTheoreticallyDominant ((lift x y).left ≫ fN.left) := by
    change IsSchemeTheoreticallyDominant (lift x y ≫ fN).left
    rw [← hw']
    exact hd
  exact ⟨bot_unique (((lift x y).left.le_ker_comp fN.left).trans_eq hdom.ker_eq_bot)⟩


open Specs.CharacterDescent (StandardLattice)
open Specs.DiagonalizableGroups (groupAlgebra)
open private extendedGroupIso from LinearAlgebraicGroups.Affine.ClosedSubgroups
open private Unipotent.multiplicativeType_iff_coordinates
  from LinearAlgebraicGroups.Unipotent.Orthogonality

private theorem torus_of_iso {T D : GroupScheme k} (e : T ≅ D) (hD : IsTorus D) :
    IsTorus T := by
  obtain ⟨E, _, _, _, r, ⟨d⟩⟩ := hD
  exact ⟨E, inferInstance, inferInstance, inferInstance, r,
    ⟨(groupBaseChange k E).mapIso e ≪≫ d⟩⟩

private theorem extendedTorus (K : Type u) [Field K] [Algebra k K]
    (T : AffineAlgebraicGroup k) (ht : IsTorus T.val) :
    IsTorus ((groupBaseChange k K).obj T.val) := by
  obtain ⟨A, _, ⟨e⟩⟩ := groupPresentation T
  have ha := (GeometricRadicals.torusCoordinateComparison A).mp (torus_of_iso e ht)
  obtain ⟨E, _, _, _, r, ⟨d⟩⟩ := ha
  let S := SeparableClosure K
  letI : Algebra k S := ((algebraMap K S).comp (algebraMap k K)).toAlgebra
  letI : IsScalarTower k K S := IsScalarTower.of_algebraMap_eq' rfl
  let a : E →ₐ[k] S := IsSepClosed.lift
  letI : Algebra E S := a.toRingHom.toAlgebra
  letI : IsScalarTower k E S := IsScalarTower.of_algebraMap_eq' a.comp_algebraMap.symm
  let dS : groupAlgebra S (StandardLattice.{u} r) ≅ extendedHopf S (extendedHopf K A) :=
    (CommHopfAlgCat.isoMk (CharacterDescent.groupAlgebraBaseChange E S _)).symm ≪≫
      (CharacterDescent.extendedHopfFunctor S).mapIso d ≪≫
      CharacterDescent.extendedHopfTower (K := E) S A ≪≫
      (CharacterDescent.extendedHopfTower (K := K) S A).symm
  exact torus_of_iso (((groupBaseChange k K).mapIso e).symm ≪≫ (extendedGroupIso K A).symm)
    ((GeometricRadicals.torusCoordinateComparison _).mpr
      ⟨S, inferInstance, inferInstance, inferInstance, r, ⟨dS⟩⟩)

private theorem kernel_isRadical {G T : AffineAlgebraicGroup k}
    {U : ClosedSubgroup G.val} {q : G.val ⟶ T.val}
    (hU : IsSmoothConnectedNormal U)
    (hu : IsUnipotent (closedSubgroupAlgebraicGroup U)) (ht : IsTorus T.val)
    (hk : IsSchemeKernel q U) : IsSolvableUnipotentRadical G U := by
  obtain ⟨A, _, ⟨a⟩⟩ := groupPresentation T
  have hmt := CharacterDescent.torusIsMultiplicativeType A
    ((GeometricRadicals.torusCoordinateComparison A).mp (torus_of_iso a ht))
  refine ⟨hU, hu, fun V hV ↦ ?_⟩
  have hzero := Unipotent.homFromUnipotentToMultiplicativeType
    (closedSubgroupAlgebraicGroup V) T (V.inclusion ≫ q) hV
    ((Unipotent.multiplicativeType_iff_coordinates a).mpr hmt)
  exact SmoothDiagonalKernel.liftToSchemeKernel hk V.inclusion hzero

theorem solvableUnipotentRadicalBaseChange : SolvableUnipotentRadicalBaseChange.{u} := by
  intro k K _ _ _ G T U q hU hu ht hq
  let h := baseChangeClosedSubgroup k K U.inclusion U.isClosedImmersion
  let U' := Specs.GeometricRadicals.baseChangedSubgroup K U h
  let G' := baseChangedAlgebraicGroup K G
  let T' := baseChangedAlgebraicGroup K T
  let q' := (groupBaseChange k K).map q
  let L := closedSubgroupAlgebraicGroup U
  let L' := closedSubgroupAlgebraicGroup (G := G') U'
  have : ConnectedSpace L.val.X.left := hU.2.1
  have : Smooth U.group.X.hom := hU.1
  have hc : GeometricallyConnected U.group.X.hom := geometricallyConnected_of_connected L
  have hs : Smooth U'.group.X.hom :=
    inferInstanceAs (Smooth (pullback.snd U.group.X.hom (fieldSpecMap k K)))
  have hcc : ConnectedSpace U'.group.X.left :=
    pullback_of_geometrically hc.geometrically_connectedSpace K (fieldSpecMap k K)
  have hn := baseChangeNormalSubgroup k K U.inclusion hU.2.2
  have he : L' = baseChangedAlgebraicGroup K L := Subtype.ext rfl
  have huu : IsUnipotent L' := he.symm ▸ (Unipotent.unipotenceFieldExtension (K := K) L).mpr hu
  have ht' : IsTorus T'.val := extendedTorus K T ht
  have hk := baseChangeKernelSquare (K := K) q U.inclusion hq.1
  have hpb := (baseChangeMapPullback (K := K) q.hom.hom).flip
  have hf : Flat q'.hom.hom.left := MorphismProperty.of_isPullback hpb hq.2.1
  have hsurj : Surjective q'.hom.hom.left := MorphismProperty.of_isPullback hpb hq.2.2.1
  have hfp : LocallyOfFinitePresentation q'.hom.hom.left :=
    MorphismProperty.of_isPullback hpb hq.2.2.2.1
  exact ⟨h, kernel_isRadical (G := G') (T := T') ⟨hs, hcc, hn⟩ huu ht' hk, ht',
    quotient_of_flat_surjective (G := G') (T := T') hk hf hsurj hfp⟩


private theorem coordinates_dim_bound (G : AffineAlgebraicGroup k) :
    ∃ b : ℕ, ringKrullDim (Specs.coordinates G.val.X) ≤ b := by
  obtain ⟨A, hA, ⟨e⟩⟩ := groupPresentation G
  obtain ⟨n, f, hf⟩ := Algebra.FiniteType.iff_quotient_mvPolynomial''.mp hA
  let e₀ : (Spec (CommRingCat.of A)) ≅ G.val.X.left :=
    (Grp.forget (SchemeOver k) ⋙ Over.forget _).mapIso e
  let e₁ := Scheme.ΓSpecIso (CommRingCat.of A)
  let e₂ := (Scheme.Γ.mapIso e₀.op) ≪≫ e₁
  exact ⟨n, by
    change ringKrullDim (Scheme.Γ.obj (op G.val.X.left)) ≤ _
    rw [ringKrullDim_eq_of_ringEquiv e₂.commRingCatIsoToRingEquiv]
    exact (ringKrullDim_le_of_surjective f.toRingHom hf).trans (by simp)⟩

private theorem dimension_of_smooth_connected (G : AffineAlgebraicGroup k)
    (hs : Smooth G.val.X.hom) (hc : ConnectedSpace G.val.X.left) :
    ∃ n : ℕ, ringKrullDim (Specs.coordinates G.val.X) = n := by
  have hi := geometricallyIrreducible_of_connected G
  have : IsIntegral G.val.X.left := (geometry_of_smooth_geometricallyIrreducible G.val.X).2.2
  have : IsDomain (Specs.coordinates G.val.X) := inferInstanceAs (IsDomain Γ(G.val.X.left, ⊤))
  obtain ⟨b, hb⟩ := coordinates_dim_bound G
  have hne : ringKrullDim (Specs.coordinates G.val.X) ≠ ⊥ :=
    mt ringKrullDim_eq_bot_iff_subsingleton.mp (not_subsingleton _)
  obtain ⟨d, hd⟩ := WithBot.ne_bot_iff_exists.mp hne
  have hdtop : d ≠ ⊤ := by
    intro he
    rw [← hd, he] at hb
    exact (not_le_of_gt (WithBot.coe_lt_coe.mpr (ENat.natCast_lt_top (n := b)))) hb
  exact ⟨d.toNat, by rw [← hd, ← ENat.natCast_toNat hdtop]; rfl⟩

private theorem iso_of_maximal_dimension {G : AffineAlgebraicGroup k} {U N : ClosedSubgroup G.val}
    (j : U.group ⟶ N.group) (hj : j ≫ N.inclusion = U.inclusion)
    (hn : IsSmoothConnectedNormal N)
    (hle : ringKrullDim (Specs.coordinates N.group.X) ≤
      ringKrullDim (Specs.coordinates U.group.X)) : IsIso j := by
  have : IsAffine U.group.X.left := (closedSubgroupAlgebraicGroup U).property.1
  have : IsAffine N.group.X.left := (closedSubgroupAlgebraicGroup N).property.1
  have : IsClosedImmersion j.hom.hom.left := GeometricRadicals.factor_closed hj
  have : ConnectedSpace N.group.X.left := hn.2.1
  have : Smooth N.group.X.hom := hn.1
  have hnconn : ConnectedSpace (closedSubgroupAlgebraicGroup N).val.X.left := hn.2.1
  have hnirr : GeometricallyIrreducible N.group.X.hom :=
    geometricallyIrreducible_of_connected (closedSubgroupAlgebraicGroup N)
  have : IsIntegral N.group.X.left := (geometry_of_smooth_geometricallyIrreducible N.group.X).2.2
  let f := j.hom.hom.left.appTop
  have hf : Function.Surjective f := j.hom.hom.left.app_surjective ⊤ (isAffineOpen_top _)
  have hinj : Function.Injective f := by
    rw [RingHom.injective_iff_ker_eq_bot]
    by_contra he
    obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot he
    have hs := ringKrullDim_succ_le_of_surjective f.hom hf
      (mem_nonZeroDivisors_of_ne_zero hx0) (show f x = 0 from hx)
    obtain ⟨b, hb⟩ := dimension_of_smooth_connected (closedSubgroupAlgebraicGroup N) hn.1 hn.2.1
    change ringKrullDim Γ(N.group.X.left, ⊤) = b at hb
    change ringKrullDim Γ(N.group.X.left, ⊤) ≤ ringKrullDim Γ(U.group.X.left, ⊤) at hle
    have hcontr := (add_le_add_left hle 1).trans hs
    rw [hb, ← Nat.cast_one, ← Nat.cast_add] at hcontr
    have hbad : b + 1 ≤ b := by exact_mod_cast hcontr
    exact Nat.not_succ_le_self b hbad
  have := IsClosedImmersion.isIso_of_injective_of_isAffine (f := j.hom.hom.left) hinj
  exact GeometricRadicals.isIso_of_schemeIso j

theorem maximalUnipotentSubgroupIsLargest : MaximalUnipotentSubgroupIsLargest.{u} := by
  intro k _ G U hU hu hm
  refine ⟨hU, hu, ?_⟩
  intro V hV hv
  obtain ⟨N, j, l, hN, hj, hl, hd⟩ := smoothNormalProduct G U V hU hV
  have hn := GeometricRadicals.unipotent_product hU.2.2 j l hj hd hu hv
  have : IsIso j := iso_of_maximal_dimension j hj hN (hm N hN hn)
  refine ⟨l ≫ inv j, ?_⟩
  rw [Category.assoc, ← hj, IsIso.inv_hom_id_assoc, hl]

theorem largestSmoothConnectedNormalUnipotentExists :
    LargestSmoothConnectedNormalUnipotentExists.{u} := by
  intro k _ G
  classical
  obtain ⟨b, hb⟩ := coordinates_dim_bound G
  have hbound (V : ClosedSubgroup G.val) : ringKrullDim (Specs.coordinates V.group.X) ≤ b := by
    have := V.isClosedImmersion
    have := G.property.1
    exact (ringKrullDim_le_of_surjective V.inclusion.hom.hom.left.appTop.hom
      (V.inclusion.hom.hom.left.app_surjective ⊤ (isAffineOpen_top _))).trans hb
  let P (n : ℕ) := ∃ V : ClosedSubgroup G.val, IsSmoothConnectedNormal V ∧
    IsUnipotent (closedSubgroupAlgebraicGroup V) ∧ ringKrullDim (Specs.coordinates V.group.X) = n
  obtain ⟨m, hm⟩ := dimension_of_smooth_connected
    (closedSubgroupAlgebraicGroup (Specs.GeometricRadicals.identitySubgroup G))
    (GeometricRadicals.identity_smoothConnectedNormal G).1
    (GeometricRadicals.identity_smoothConnectedNormal G).2.1
  have hmb : m ≤ b := by exact_mod_cast hm ▸ hbound (Specs.GeometricRadicals.identitySubgroup G)
  obtain ⟨U, hU, hu, hd⟩ := Nat.findGreatest_spec (P := P) hmb
    ⟨_, GeometricRadicals.identity_smoothConnectedNormal G, GeometricRadicals.identity_unipotent G, hm⟩
  refine ⟨U, maximalUnipotentSubgroupIsLargest G U hU hu ?_⟩
  intro V hV hv
  obtain ⟨n, hn⟩ := dimension_of_smooth_connected (closedSubgroupAlgebraicGroup V) hV.1 hV.2.1
  have hnb : n ≤ b := by exact_mod_cast hn ▸ hbound V
  change ringKrullDim (Specs.coordinates V.group.X) = n at hn
  rw [hd, hn]
  exact_mod_cast Nat.le_findGreatest hnb (show P n from ⟨V, hV, hv, hn⟩)


open private GeometricRadicals.sectionsMap GeometricRadicals.solvable_iff_sections
  from LinearAlgebraicGroups.Reductive.GeometricRadicals
open Specs.SchemeDerivedGroup (DerivedSeries)

private theorem derivedSeries_le_sections {G H : GroupScheme k} {n : ℕ}
    (h : DerivedSeries G n H) (X : SchemeOver k) :
    ∃ i : H ⟶ G, derivedSeries (X ⟶ G.X) n ≤ (GeometricRadicals.sectionsMap i X).range := by
  induction h with
  | zero =>
    refine ⟨𝟙 G, fun x _ ↦ ⟨x, ?_⟩⟩
    change x ≫ 𝟙 G.X = x
    exact Category.comp_id _
  | @succ n H previous D hD ih =>
    obtain ⟨i, hi⟩ := ih
    refine ⟨D.inclusion ≫ i, ?_⟩
    let f := GeometricRadicals.sectionsMap i X
    let g := GeometricRadicals.sectionsMap D.inclusion X
    have hD' : commutator (X ⟶ H.X) ≤ g.range :=
      SchemeDerivedGroup.commutatorSubgroupLe D hD X
    change derivedSeries (X ⟶ G.X) (n + 1) ≤ (f.comp g).range
    rw [MonoidHom.range_comp, derivedSeries_succ]
    refine (Subgroup.commutator_mono hi hi).trans ?_
    change ⁅f.range, f.range⁆ ≤ g.range.map f
    rw [← map_commutator_eq]
    exact Subgroup.map_mono hD' 

private theorem solvable_sections {G : GroupScheme k} (h : IsSolvable G) (X : SchemeOver k) :
    Group.IsSolvable (X ⟶ G.X) := by
  obtain ⟨n, H, hH, ⟨e⟩⟩ := h
  obtain ⟨i, hi⟩ := derivedSeries_le_sections hH X
  refine ⟨n, le_antisymm (hi.trans ?_) bot_le⟩
  rintro z ⟨x, rfl⟩
  have hm : Mono e.hom.hom.hom := inferInstance
  have hx : x = 1 := (cancel_mono e.hom.hom.hom).mp
    ((isTerminalTensorUnit (C := SchemeOver k)).hom_ext _ _)
  rw [hx, map_one]
  exact Subgroup.one_mem _

private theorem solvable_after_algClosed_extension (L : Type u) [Field L] [Algebra k L]
    [IsAlgClosed L] (G : AffineAlgebraicGroup k) (hs : Smooth G.val.X.hom)
    (hc : ConnectedSpace G.val.X.left) (hv : IsSolvable G.val) :
    IsSolvable (baseChangedAlgebraicGroup L G).val := by
  let G' := baseChangedAlgebraicGroup L G
  have hs' : Smooth G'.val.X.hom :=
    inferInstanceAs (Smooth (pullback.snd G.val.X.hom (fieldSpecMap k L)))
  have hgc : GeometricallyConnected G.val.X.hom := geometricallyConnected_of_connected G
  have hc' : ConnectedSpace G'.val.X.left :=
    pullback_of_geometrically hgc.geometrically_connectedSpace L (fieldSpecMap k L)
  apply (GeometricRadicals.solvable_iff_sections G' hs' hc').mpr
  let R := CommAlgCat.of L L
  let b : (testSpec L).obj (op R) ≅ 𝟙_ (SchemeOver L) :=
    Over.isoMk (Iso.refl _) (by
      change 𝟙 (Spec (CommRingCat.of L)) ≫ 𝟙 _ =
        Spec.map (CommRingCat.ofHom (algebraMap L L))
      simp [Algebra.algebraMap_self])
  let X := (testSpec k).obj (op ((restrictTestAlgebra k L).obj R))
  have hX := solvable_sections hv X
  let e : (𝟙_ (SchemeOver L) ⟶ G'.val.X) ≃* (X ⟶ G.val.X) :=
    { toEquiv := (Iso.homCongr b.symm (Iso.refl _)).trans
        (baseChangePointGroupEquiv L G.val R).toEquiv
      map_mul' := by
        intro x y
        change baseChangePointGroupEquiv L G.val R (b.hom ≫ (x * y)) =
          baseChangePointGroupEquiv L G.val R (b.hom ≫ x) *
            baseChangePointGroupEquiv L G.val R (b.hom ≫ y)
        have he : b.hom ≫ (x * y) = (b.hom ≫ x) * (b.hom ≫ y) :=
          MonObj.comp_mul b.hom x y
        exact (congrArg (baseChangePointGroupEquiv L G.val R) he).trans (map_mul _ _ _) }
  exact Group.isSolvable_of_isSolvable_injective (f := e.toMonoidHom) e.injective


open Specs.CharacterDescent (CharacterModule GeometricCharacters)
open private CharacterDescent.geometricActionContinuous CharacterDescent.finiteModelOfCharacters
  CharacterDescent.groupLikeIso CharacterDescent.groupLikeSpanOfSplit
  CharacterDescent.groupAlgebraOfCharacters CharacterDescent.groupAlgebraOfCharacters_hom_single
  CharacterDescent.descendEquivariantHopfMap CharacterDescent.includeScalarExtension_injective
  from LinearAlgebraicGroups.Multiplicative.CharacterDescent
open private DiagonalizableGroups.liftCharacters DiagonalizableGroups.liftCharacters_single
  DiagonalizableGroups.liftCharacters_injective DiagonalizableGroups.groupAlgebraMap_injective
  DiagonalizableGroups.groupAlgebraMap_surjective
  from LinearAlgebraicGroups.Multiplicative.DiagonalizableGroups
open private SchemeDerivedGroup.quotient_desc SchemeDerivedGroup.kernel_normal
  from LinearAlgebraicGroups.Solvable.SchemeDerivedGroup
open private fppfYoneda_locallySurjective schemeKernel_exists
  from LinearAlgebraicGroups.Affine.SchemeImageQuotient
open private Unipotent.faithfullyFlat_of_presentation
  from LinearAlgebraicGroups.Unipotent.ExactOperations

private theorem torusCoordinatesSplit [IsAlgClosed k] (B : HopfAlgebraCategory k)
    (h : Specs.CharacterDescent.IsTorus B) :
    ∃ r : ℕ, Nonempty (groupAlgebra k (StandardLattice.{u} r) ≅ B) := by
  obtain ⟨E, _, _, _, r, ⟨d⟩⟩ := h
  let a : E →ₐ[k] k := IsSepClosed.lift
  letI : Algebra E k := a.toRingHom.toAlgebra
  letI : IsScalarTower k E k := IsScalarTower.of_algebraMap_eq' a.comp_algebraMap.symm
  exact ⟨r, ⟨(CommHopfAlgCat.isoMk (CharacterDescent.groupAlgebraBaseChange E k _)).symm ≪≫
    (CharacterDescent.extendedHopfFunctor k).mapIso d ≪≫
    CharacterDescent.extendedHopfTower (K := E) k B ≪≫
    CommHopfAlgCat.isoMk (Bialgebra.TensorProduct.lid k B)⟩⟩

private theorem quotient_characters {G Q : AffineAlgebraicGroup k}
    {U : ClosedSubgroup G.val} {q : G.val ⟶ Q.val}
    (hQ : IsFppfGroupQuotient (G := G) (Q := Q) U q)
    (hu : IsUnipotent (closedSubgroupAlgebraicGroup U))
    {B A : HopfAlgebraCategory k} (a : B ⟶ A)
    (eG : specGroup A ≅ G.val) (eQ : specGroup B ≅ Q.val)
    (ha : specGroupMap a ≫ eQ.hom = eG.hom ≫ q) :
    Function.Bijective (CharacterDescent.mapGroupLike a) := by
  have hinj := (Unipotent.faithfullyFlat_of_presentation q a eG eQ ha hQ.2.1 hQ.2.2.1).injective
  refine ⟨fun x y h ↦ GroupLike.val_injective (hinj (congrArg GroupLike.val h)), ?_⟩
  intro x
  let M := Specs.DiagonalizableGroups.IntegerCharacters.{u}
  let i : Multiplicative ℤ ≃* M := MulEquiv.ulift.symm
  letI : Group.FG M := Group.fg_of_surjective (f := i.toMonoidHom) i.surjective
  let Z := Specs.StandardGroups.spectrum k (MonoidAlgebra k M)
  have hZ : (Specs.CharacterDescent.multiplicativeTypeSpecFunctor k).essImage Z := by
    apply (Unipotent.multiplicativeType_iff_coordinates
      (G := Z) (A := groupAlgebra k M) (Iso.refl _)).mpr
    exact ⟨k, inferInstance, inferInstance, inferInstance,
      ⟨⟨CommGrpCat.of M, inferInstance⟩,
        ⟨(CommHopfAlgCat.isoMk (CharacterDescent.groupAlgebraBaseChange k k M)).symm⟩⟩⟩
  obtain ⟨c, hnat, _⟩ := CharacterDescent.characterInterpretation (k := k)
  let χ : G.val ⟶ Z.val := eG.inv ≫ c A x
  have hzero := Unipotent.homFromUnipotentToMultiplicativeType
    (closedSubgroupAlgebraicGroup U) Z (U.inclusion ≫ χ) hu hZ
  have hkill {X : SchemeOver k} (t : X ⟶ G.val.X) (ht : Specs.SchemeDerivedGroup.FactorsThrough U t) :
      t ≫ χ.hom.hom = 1 := by
    obtain ⟨z, hz⟩ := ht
    change z ≫ U.inclusion.hom.hom = t at hz
    have h₀ : U.inclusion.hom.hom ≫ χ.hom.hom = 1 :=
      congrArg (fun f : U.group ⟶ Z.val ↦ f.hom.hom) hzero
    rw [← hz, Category.assoc, h₀, MonObj.comp_one]
  have : Flat q.hom.hom.left := hQ.2.1
  have : Surjective q.hom.hom.left := hQ.2.2.1
  have : LocallyOfFinitePresentation q.hom.hom.left := hQ.2.2.2.1
  obtain ⟨ψ, hψ, _⟩ := SchemeDerivedGroup.quotient_desc Q U q hQ.2.2.2.2
    (fppfYoneda_locallySurjective q.hom.hom) χ hkill
  let y := (c B).symm (eQ.hom ≫ ψ)
  refine ⟨y, (c A).injective ?_⟩
  change c A ⟨a.hom y.val, y.2.map a.hom⟩ = c A x
  rw [hnat]
  have hcy : c B y = eQ.hom ≫ ψ := (c B).apply_symm_apply _
  rw [hcy]
  change specGroupMap a ≫ (eQ.hom ≫ ψ) = (c A) x
  rw [← Category.assoc, ha, Category.assoc, hψ]
  simp [χ]

/-- The intrinsic geometric character group descends to a torus. Its inclusion
in the geometric coordinate algebra descends as a Hopf map. -/
private theorem descend_character_quotient (L : Type u) [Field L] [Algebra k L]
    [IsSepClosure k L] (A : HopfAlgebraCategory k) (B : HopfAlgebraCategory L)
    (a : B ⟶ extendedHopf L A) (ha : Function.Bijective (CharacterDescent.mapGroupLike a))
    (r : ℕ) (d : groupAlgebra L (StandardLattice.{u} r) ≅ B) :
    ∃ (C : HopfAlgebraCategory k) (_ : Algebra.FiniteType k C)
      (f : C ⟶ A) (e : extendedHopf L C ≅ B),
      extendedHopfMap L f = e.hom ≫ a := by
  let lattice := (CharacterDescent.monomialCharacterEquiv L).trans
    ((CharacterDescent.groupLikeIso d).trans (MulEquiv.ofBijective _ ha))
  have hFG : Group.FG (StandardLattice.{u} r) := by
    let i : Multiplicative ℤ ≃* Specs.DiagonalizableGroups.IntegerCharacters.{u} := MulEquiv.ulift.symm
    have : Group.FG Specs.DiagonalizableGroups.IntegerCharacters.{u} :=
      Group.fg_of_surjective (f := i.toMonoidHom) i.surjective
    apply Group.fg_def.mpr
    simpa only [Subgroup.pi_top] using
      (Subgroup.FG.pi (P := fun (_ : Fin r) => (⊤ : Subgroup Specs.DiagonalizableGroups.IntegerCharacters))
        fun _ => Group.fg_def.mp inferInstance)
  have : Group.FG (GeometricCharacters L A) :=
    Group.fg_of_surjective (f := lattice.toMonoidHom) lattice.surjective
  let M : CharacterModule k L :=
    ⟨⟨CommGrpCat.of (GeometricCharacters L A), CharacterDescent.geometricAction L A⟩,
      inferInstance, CharacterDescent.geometricActionContinuous L A⟩
  obtain ⟨D, _, _, _, _, ⟨eM⟩⟩ := CharacterDescent.finiteModelOfCharacters L M
  let C := D.obj.val
  let C' := extendedHopf L C
  let co := eM.hom.hom.hom.hom
  have hr : Function.Bijective co := by
    let z : IsIso eM.hom.hom.hom := by
      let F := (CategoryTheory.ObjectProperty.ι _ : CharacterModule k L ⥤ _) ⋙
        Action.forget CommGrpCat (Gal(L/k))
      exact F.map_isIso eM.hom
    exact ConcreteCategory.bijective_of_isIso eM.hom.hom.hom
  let g : GroupLike L C' ≃* GroupLike L B :=
    (MulEquiv.ofBijective co hr).trans (MulEquiv.ofBijective _ ha).symm
  have hCD := (CharacterDescent.splitsOverSeparableClosure (K := L) C).mp D.property
  let hspan := CharacterDescent.groupLikeSpanOfSplit C' hCD
  let t := CharacterDescent.groupAlgebraOfCharacters C' hspan
  let u := CharacterDescent.groupAlgebraOfCharacters B
    (CharacterDescent.groupLikeSpanOfSplit B
      ⟨⟨CommGrpCat.of _, hFG⟩, ⟨d⟩⟩)
  let gHom := MonoidAlgebra.mapDomainBialgHom L g.toMonoidHom
  have hgHom : Function.Bijective gHom :=
    ⟨DiagonalizableGroups.groupAlgebraMap_injective (k := L) g.toMonoidHom g.injective,
      DiagonalizableGroups.groupAlgebraMap_surjective (k := L) g.toMonoidHom g.surjective⟩
  let gIso : groupAlgebra L (GroupLike L C') ≅ groupAlgebra L (GroupLike L B) :=
    CommHopfAlgCat.isoMk (BialgEquiv.ofBijective gHom hgHom)
  let e : C' ≅ B := t.symm ≪≫ gIso ≪≫ u
  let p : C' ⟶ extendedHopf L A := e.hom ≫ a
  have hp (x : GroupLike L C') : p.hom x.val = (co x).val := by
    rw [← CharacterDescent.groupAlgebraOfCharacters_hom_single L hspan x]
    change (t.hom ≫ p).hom (MonoidAlgebra.single x 1) = _
    rw [show t.hom ≫ p = gIso.hom ≫ u.hom ≫ a by simp [p, e, Category.assoc]]
    change a.hom (u.hom.hom (MonoidAlgebra.mapDomainBialgHom L g.toMonoidHom
      (MonoidAlgebra.single x 1))) = _
    rw [MonoidAlgebra.mapDomainBialgHom_single, CharacterDescent.groupAlgebraOfCharacters_hom_single]
    exact congrArg GroupLike.val ((MulEquiv.ofBijective _ ha).apply_symm_apply (co x))
  let S := CharacterDescent.scalarExtensionDatum L C
  let T := CharacterDescent.scalarExtensionDatum L A
  have heq : S.Equivariant T p := by
    intro σ x
    obtain ⟨y, rfl⟩ := (CommHopfAlgCat.ofIso t).surjective x
    change p.hom (S.action.act σ (t.hom.hom y)) = T.action.act σ (p.hom (t.hom.hom y))
    induction y using MonoidAlgebra.induction_linear with
    | zero => simp
    | add x y hx hy => simp only [map_add, hx, hy]
    | single x r =>
      rw [show MonoidAlgebra.single x r = r • MonoidAlgebra.single x (1 : L) by simp,
        map_smul, CharacterDescent.groupAlgebraOfCharacters_hom_single, S.action.map_smul,
        map_smul, map_smul, hp, T.action.map_smul]
      have hcomm := DFunLike.congr_fun (congrArg CommGrpCat.Hom.hom (eM.hom.hom.comm σ)) x
      change co ((CharacterDescent.geometricAction L C σ).asHom x) =
        (CharacterDescent.geometricAction L A σ).asHom (co x) at hcomm
      congr 1
      change p.hom (((CharacterDescent.geometricAction L C σ).asHom x).val) = _
      rw [hp]
      exact congrArg GroupLike.val hcomm
  obtain ⟨f, hf⟩ := CharacterDescent.descendEquivariantHopfMap L p heq
  exact ⟨C, D.obj.property, f, e, hf⟩


open private SmoothDiagonalKernel.extendedGroupIso_naturality
  from LinearAlgebraicGroups.Solvable.SmoothDiagonalKernel
open private specGroupMap_comp from LinearAlgebraicGroups.Affine.ClosedSubgroups

private theorem subgroupKernelIso {G D T : GroupScheme k} {p : G ⟶ D} {q : G ⟶ T}
    {U V : ClosedSubgroup G} (hu : IsSchemeKernel p U) (hv : IsSchemeKernel q V)
    (e : D ≅ T) (hpq : p ≫ e.hom = q) : Nonempty (U.group ≅ V.group) := by
  have huz : U.inclusion ≫ p = 0 := Grp.hom_ext _ _ hu.w
  have hvz : V.inclusion ≫ q = 0 := Grp.hom_ext _ _ hv.w
  obtain ⟨i, hi⟩ := SmoothDiagonalKernel.liftToSchemeKernel hv U.inclusion
    (by rw [← hpq, ← Category.assoc, huz, zero_comp])
  obtain ⟨j, hj⟩ := SmoothDiagonalKernel.liftToSchemeKernel hu V.inclusion
    (by apply (cancel_mono e.hom).mp; rw [Category.assoc, hpq, hvz, zero_comp])
  let F := Grp.forget (SchemeOver k) ⋙ Over.forget (Spec (CommRingCat.of k))
  have : IsClosedImmersion (F.map U.inclusion) := U.isClosedImmersion
  have : IsClosedImmersion (F.map V.inclusion) := V.isClosedImmersion
  have : Mono U.inclusion := F.mono_of_mono_map inferInstance
  have : Mono V.inclusion := F.mono_of_mono_map inferInstance
  exact ⟨⟨i, j, (cancel_mono U.inclusion).mp (by rw [Category.assoc, hj, hi, Category.id_comp]),
    (cancel_mono V.inclusion).mp (by rw [Category.assoc, hi, hj, Category.id_comp])⟩⟩

private theorem kernel_geometry_of_extension (L : Type u) [Field L] [Algebra k L]
    {G : AffineAlgebraicGroup k} {U : ClosedSubgroup G.val}
    {W : ClosedSubgroup (baseChangedAlgebraicGroup L G).val}
    (e : (groupBaseChange k L).obj U.group ≅ W.group)
    (hs : Smooth W.group.X.hom) (hc : ConnectedSpace W.group.X.left)
    (hu : IsUnipotent (closedSubgroupAlgebraicGroup W)) :
    Smooth U.group.X.hom ∧ ConnectedSpace U.group.X.left ∧
      IsUnipotent (closedSubgroupAlgebraicGroup U) := by
  let U₀ := closedSubgroupAlgebraicGroup U
  let U' := baseChangedAlgebraicGroup L U₀
  let W₀ := closedSubgroupAlgebraicGroup W
  let F := Grp.forget (SchemeOver L) ⋙ Over.forget (Spec (CommRingCat.of L))
  let e₀ := F.mapIso e
  have hsc : Smooth U'.val.X.hom := by
    change Smooth ((groupBaseChange k L).obj U.group).X.hom
    rw [← e.hom.hom.hom.w]
    have : IsIso e.hom.hom.hom.left := F.map_isIso e.hom
    exact smooth_comp _ _
  have hc' : ConnectedSpace U'.val.X.left := e₀.hom.homeomorph.connectedSpace_iff.mpr hc
  let p : U'.val.X.left ⟶ U.group.X.left := pullback.fst U.group.X.hom (fieldSpecMap k L)
  have hsu : Surjective p :=
    MorphismProperty.of_isPullback (IsPullback.of_hasPullback U.group.X.hom (fieldSpecMap k L)).flip
      (inferInstance : Surjective (fieldSpecMap k L))
  have : IsIso e.inv.hom.hom.left := F.map_isIso e.inv
  have hf : Flat e.inv.hom.hom.left := inferInstance
  have hs' : Surjective e.inv.hom.hom.left := inferInstance
  have hu' : IsUnipotent U' :=
    Unipotent.faithfullyFlatQuotientsUnipotent W₀ U' e.inv hf hs' hu
  exact ⟨smooth_of_smooth_after_fieldExtension U.group.X.hom hsc,
    hsu.1.connectedSpace p.continuous,
    (Unipotent.unipotenceFieldExtension (K := L) U₀).mp hu'⟩

theorem solvableUnipotentRadicalExists : SolvableUnipotentRadicalExists.{u} := by
  intro k _ _ G hs hc hv
  let L := AlgebraicClosure k
  let G' := baseChangedAlgebraicGroup L G
  let F := groupBaseChange k L
  have hs' : Smooth G'.val.X.hom :=
    inferInstanceAs (Smooth (pullback.snd G.val.X.hom (fieldSpecMap k L)))
  have hgc : GeometricallyConnected G.val.X.hom := geometricallyConnected_of_connected G
  have hc' : ConnectedSpace G'.val.X.left :=
    pullback_of_geometrically hgc.geometrically_connectedSpace L (fieldSpecMap k L)
  obtain ⟨W, D, p, hW, hD, hp⟩ :=
    geometricRadicalQuotient G' hs' hc' (solvable_after_algClosed_extension L G hs hc hv)
  obtain ⟨A, hA, ⟨eG⟩⟩ := groupPresentation G
  obtain ⟨B, hB, ⟨eD⟩⟩ := groupPresentation D
  let eG' := extendedGroupIso L A ≪≫ F.mapIso eG
  let ff := hopfSpec.fullyFaithful (R := CommRingCat.of L)
  let a : B ⟶ extendedHopf L A := (ff.preimage (eG'.hom ≫ p ≫ eD.inv)).unop
  have ha : specGroupMap a ≫ eD.hom = eG'.hom ≫ p := by
    have hh : specGroupMap a = eG'.hom ≫ p ≫ eD.inv := ff.map_preimage _
    rw [hh]
    simp
  have hqa := quotient_characters hp hW.2.1 a eG' eD ha
  obtain ⟨r, ⟨d⟩⟩ := torusCoordinatesSplit B
    ((GeometricRadicals.torusCoordinateComparison B).mp (torus_of_iso eD hD))
  obtain ⟨C, hC, f, e, hf⟩ := descend_character_quotient L A B a hqa r d
  let T := Specs.StandardGroups.spectrum k C
  have ht : IsTorus T.val := (GeometricRadicals.torusCoordinateComparison C).mpr
    ⟨L, inferInstance, inferInstance, inferInstance, r, ⟨d ≪≫ e.symm⟩⟩
  let q : G.val ⟶ T.val := eG.inv ≫ specGroupMap f
  have hTi : IsAffine T.val.X.left := T.property.1
  obtain ⟨U, hU⟩ := schemeKernel_exists q
  have hcU := baseChangeClosedSubgroup k L U.inclusion U.isClosedImmersion
  let U' := Specs.GeometricRadicals.baseChangedSubgroup L U hcU
  let w := (hopfSpec (CommRingCat.of L)).mapIso e.op
  let v : (F.obj T.val) ≅ D.val := (extendedGroupIso L C).symm ≪≫ w.symm ≪≫ eD
  have hq : F.map q ≫ v.hom = p := by
    apply (cancel_epi eG'.hom).mp
    have hq₀ : F.map eG.hom ≫ F.map q = F.map (specGroupMap f) := by
      rw [← F.map_comp]
      exact congrArg F.map (Iso.hom_inv_id_assoc eG (specGroupMap f))
    have h₀ : eG'.hom ≫ F.map q =
        specGroupMap (extendedHopfMap L f) ≫ (extendedGroupIso L C).hom := by
      change ((extendedGroupIso L A).hom ≫ F.map eG.hom) ≫ F.map q = _
      rw [Category.assoc, hq₀]
      exact (SmoothDiagonalKernel.extendedGroupIso_naturality L f).symm
    rw [← Category.assoc, h₀, hf, specGroupMap_comp]
    change ((specGroupMap a ≫ w.hom) ≫ (extendedGroupIso L C).hom) ≫
      ((extendedGroupIso L C).inv ≫ w.inv ≫ eD.hom) = _
    rw [Category.assoc, Iso.hom_inv_id_assoc, Category.assoc, Iso.hom_inv_id_assoc]
    exact ha
  have hk' : IsSchemeKernel (F.map q) U' := baseChangeKernelSquare q U.inclusion hU
  obtain ⟨i⟩ := subgroupKernelIso hk' hp.1 v hq
  obtain ⟨hUs, hUc, hUu⟩ := kernel_geometry_of_extension L (U := U) (W := W)
    i hW.1.1 hW.1.2.1 hW.2.1
  have hfi : Function.Injective f.hom := by
    have hAi := (Unipotent.faithfullyFlat_of_presentation p a eG' eD ha hp.2.1 hp.2.2.1).injective
    have hcomp : Function.Injective (extendedHopfMap L f).hom := by
      rw [hf]
      exact hAi.comp (CommHopfAlgCat.ofIso e).injective
    intro x y hxy
    apply CharacterDescent.includeScalarExtension_injective L C
    apply hcomp
    change (1 : L) ⊗ₜ[k] f.hom x = (1 : L) ⊗ₜ[k] f.hom y
    rw [hxy]
  let b := CommRingCat.ofHom f.hom.toAlgHom.toRingHom
  have hflat := (flat_and_surjective_SpecMap_iff b).mpr (hopfFaithfulFlatness k f hfi)
  have : IsNoetherianRing C := Algebra.FiniteType.isNoetherianRing k C
  have hbft : b.hom.FiniteType := RingHom.FiniteType.of_comp_finiteType
    (f := algebraMap k C) (by
      rw [show b.hom.comp (algebraMap k C) = algebraMap k A from f.hom.toAlgHom.comp_algebraMap]
      exact RingHom.finiteType_algebraMap.mpr hA)
  have hfp := (LocallyOfFinitePresentation.SpecMap_iff b).mpr
    (RingHom.FinitePresentation.of_finiteType.mp hbft)
  let J := Grp.forget (SchemeOver k) ⋙ Over.forget (Spec (CommRingCat.of k))
  have : IsIso eG.inv.hom.hom.left := J.map_isIso eG.inv
  have : Flat (specGroupMap f).hom.hom.left := hflat.1
  have : Surjective (specGroupMap f).hom.hom.left := hflat.2
  have : LocallyOfFinitePresentation (specGroupMap f).hom.hom.left := hfp
  have hqfp : IsFppfGroupQuotient (G := G) (Q := T) U q :=
    quotient_of_flat_surjective hU
      (inferInstanceAs (Flat (eG.inv.hom.hom.left ≫ (specGroupMap f).hom.hom.left)))
      (inferInstanceAs (Surjective (eG.inv.hom.hom.left ≫ (specGroupMap f).hom.hom.left)))
      (inferInstanceAs (LocallyOfFinitePresentation
        (eG.inv.hom.hom.left ≫ (specGroupMap f).hom.hom.left)))
  exact ⟨U, T, q,
    kernel_isRadical (G := G) (T := T) ⟨hUs, hUc, SchemeDerivedGroup.kernel_normal hU⟩ hUu ht hU,
    ht, hqfp⟩


end
end LinearAlgebraicGroups.SolvableRadical
