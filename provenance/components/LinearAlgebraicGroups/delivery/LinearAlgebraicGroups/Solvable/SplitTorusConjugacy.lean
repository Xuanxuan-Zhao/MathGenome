import Specs.LinearAlgebraicGroups.Solvable.SplitTorusConjugacy
import Specs.LinearAlgebraicGroups.Reductive.MaximalToriExist
import LinearAlgebraicGroups.Affine.Components
import LinearAlgebraicGroups.Descent.FiniteFieldFlags
import LinearAlgebraicGroups.Reductive.TorusFreeUnipotent
import LinearAlgebraicGroups.Solvable.SplitSolvableRadical
import LinearAlgebraicGroups.Solvable.TorusLimitFactorization
import Mathlib.AlgebraicGeometry.Morphisms.FlatMono
import Batteries.Tactic.OpenPrivate

import LinearAlgebraicGroups.Reductive.MaximalToriExist
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

universe u

namespace LinearAlgebraicGroups.SplitTorusConjugacy

open _root_.LinearAlgebraicGroups.Specs
open Specs.SplitTorusConjugacy
open Specs.GeometricBorelConjugacy (subgroupOfSubgroup)
open Specs.GeometricRadicals (IsSplitTorus IsTorus IsMaximalTorus baseChangedSubgroup)
open Specs.GeometricTorusSplitting (IsUnipotentRadical subgroupProduct)
open Specs.SchemeDerivedGroup (IsSplitSolvable IsSubgroupOf IsSolvable)
open Specs.Unipotent (IsFppfGroupQuotient IsUnipotent baseChangedAlgebraicGroup
  closedSubgroupAlgebraicGroup)
open Specs.StandardGroups (multiplicativePowerGroup)
open LinearAlgebraicGroups.StandardGroups (multiplicativePowerGroupPointsIso)

open private underlyingFunctor isoOfPointIso normalOfSchemeKernel
  from LinearAlgebraicGroups.Solvable.SmoothDiagonalKernel
open private centralizes_iff mono_over comp_conjugateFamily extensionAdj adjoint_family
  prodComparison_inv_fst conjugation conjugation_baseChange whisker_conjugation familyFactorizationLocus
  from LinearAlgebraicGroups.Affine.Stabilizers
open private factorsThrough_iff_cover overCoverObj overCoverMap isIso_over_product_map
  from LinearAlgebraicGroups.Affine.FixedPointSchemes
open private affine_tensor from LinearAlgebraicGroups.Solvable.FiniteWordClosure
open private isIso_of_schemeIso solvable_iff_sections rationalSections rationalMap factor_closed
  from LinearAlgebraicGroups.Reductive.GeometricRadicals
open private baseChangeMapPullback baseChangeKernelSquare
  from LinearAlgebraicGroups.Affine.Components
open private isTorus_of_split splitTorus_baseChange
  from LinearAlgebraicGroups.Descent.FiniteFieldFlags
open private closed_of_section product_isIso maximal_of_iso_projection
  iso_projection_of_maximal torus_of_split torus_multiplicativeType section_conjugates_lift
  from LinearAlgebraicGroups.Solvable.GeometricTorusSplitting
open private splitSolvableGeometry
  from LinearAlgebraicGroups.Solvable.SplitSolvableRadical
open private represented_quotient_of_kernel
  from LinearAlgebraicGroups.Unipotent.PerfectFieldSplitness
open private solvable_maximal_torus_iff inclusion_mono
  from LinearAlgebraicGroups.Reductive.MaximalToriConjugate
open private unipotent_sections_solvable solvable_of_schemeKernel torus_commutative
  from LinearAlgebraicGroups.Reductive.TorusFreeUnipotent
open private torus_smooth_connected_solvable subgroupOf_mutual_iso
  from LinearAlgebraicGroups.Reductive.GeometricBorelConjugacy
open private isMonHom_of_comp_closed schemeKernel_sections
  from LinearAlgebraicGroups.Affine.SchemeImageQuotient

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false
set_option maxHeartbeats 1200000

variable {k : Type u} [Field k]

private theorem splitTorus_iff_points (G : AffineAlgebraicGroup k) :
    IsSplitTorus G.val ↔ Specs.SplitSolvableRadical.IsSplitTorus G := by
  constructor
  · rintro ⟨r, ⟨e⟩⟩
    exact ⟨r, ⟨(groupPointsFunctor k).mapIso e ≪≫
      multiplicativePowerGroupPointsIso k (Unipotent.Index r)⟩⟩
  · rintro ⟨r, ⟨e⟩⟩
    exact ⟨r, ⟨isoOfPointIso G (multiplicativePowerGroup k (Unipotent.Index r))
      (e ≪≫ (multiplicativePowerGroupPointsIso k (Unipotent.Index r)).symm)⟩⟩

private theorem diagonalQuotient (G : AffineAlgebraicGroup k) (hG : IsSplitSolvable G.val) :
    ∃ (U : ClosedSubgroup G.val) (D : AffineAlgebraicGroup k) (p : G.val ⟶ D.val),
      IsUnipotentRadical U ∧ GeometricallyConnected U.group.X.hom ∧
        IsFppfGroupQuotient U p ∧ IsSplitTorus D.val := by
  obtain ⟨n, H, j, e, hj, htri⟩ := SplitSolvableRadical.faithfulTriangularization G hG
  let I := Unipotent.Index.{u} n
  obtain ⟨d, D, p, i, U, h, _⟩ := SplitSolvableRadical.splitKernelOfTriangularization n G H
    (multiplicativePowerGroup k I) j e (multiplicativePowerGroupPointsIso k I) hG hj htri
  obtain ⟨_, _, _, _, hp, hD, hs, hc, hn, hu, hmax⟩ := h
  letI := hc
  exact ⟨U, D, p, ⟨hs, GeometricallyConnected.connectedSpace_of_subsingleton (f := U.group.X.hom),
    hn, hu, hmax⟩,
    hc, hp, (splitTorus_iff_points D).mpr hD⟩

private theorem fieldBaseChangeClosed (K : Type u) [Field K] [Algebra k K]
    {G H : GroupScheme k} {f : G ⟶ H} (hf : IsClosedImmersion f.hom.hom.left) :
    IsClosedImmersion ((groupBaseChange k K).map f).hom.hom.left :=
  MorphismProperty.of_isPullback (baseChangeMapPullback (K := K) f.hom.hom).flip hf

private def extendSubgroup (K : Type u) [Field K] [Algebra k K]
    {G : GroupScheme k} (T : ClosedSubgroup G) : ClosedSubgroup ((groupBaseChange k K).obj G) :=
  baseChangedSubgroup K T (fieldBaseChangeClosed K T.isClosedImmersion)

private theorem baseChangeReflectsIso (K : Type u) [Field K] [Algebra k K]
    {G H : GroupScheme k} (f : G ⟶ H) [IsIso ((groupBaseChange k K).map f)] :
    IsIso f := by
  suffices h : IsIso f.hom.hom.left from isIso_of_schemeIso f
  let b := ((groupBaseChange k K).map f).hom.hom.left
  haveI : IsIso b := (underlyingFunctor K).map_isIso ((groupBaseChange k K).map f)
  let π := pullback.fst H.X.hom (fieldSpecMap k K)
  have surj : Surjective (fieldSpecMap k K) := ⟨fun _ ↦
    ⟨IsLocalRing.closedPoint K, Subsingleton.elim _ _⟩⟩
  haveI : Surjective π := inferInstanceAs (Surjective (pullback.fst H.X.hom _))
  haveI : Flat (fieldSpecMap k K) := inferInstance
  haveI : Flat π := inferInstanceAs (Flat (pullback.fst H.X.hom _))
  haveI : QuasiCompact π := inferInstanceAs (QuasiCompact (pullback.fst H.X.hom _))
  exact MorphismProperty.of_isPullback_of_descendsAlong
    (P := MorphismProperty.isomorphisms Scheme.{u}) (Q := @Surjective ⊓ @Flat ⊓ @QuasiCompact)
    (baseChangeMapPullback (K := K) f.hom.hom)
    (show (Surjective π ∧ Flat π) ∧ QuasiCompact π from
      ⟨⟨inferInstance, inferInstance⟩, inferInstance⟩)
    (show IsIso b from inferInstance)

private theorem splitAfterBaseChange (K : Type u) [Field K] [Algebra k K]
    {G : GroupScheme k} (h : IsSplitTorus G) : IsSplitTorus ((groupBaseChange k K).obj G) := by
  obtain ⟨r, ⟨e⟩⟩ := h
  obtain ⟨d⟩ := splitTorus_baseChange (k := k) K r
  exact ⟨r, ⟨(groupBaseChange k K).mapIso e ≪≫ d⟩⟩

private theorem quotientAfterBaseChange (K : Type u) [Field K] [Algebra k K]
    {G D : AffineAlgebraicGroup k} {U : ClosedSubgroup G.val} {p : G.val ⟶ D.val}
    (hp : IsFppfGroupQuotient U p) :
    IsFppfGroupQuotient (G := baseChangedAlgebraicGroup K G) (Q := baseChangedAlgebraicGroup K D)
      (extendSubgroup K U) ((groupBaseChange k K).map p) := by
  have h := (baseChangeMapPullback (K := K) p.hom.hom).flip
  exact represented_quotient_of_kernel _ _ (baseChangeKernelSquare p U.inclusion hp.1)
    (MorphismProperty.of_isPullback h hp.2.1)
    (MorphismProperty.of_isPullback h hp.2.2.1)
    (MorphismProperty.of_isPullback h hp.2.2.2.1)

private theorem radicalAfterBaseChange (K : Type u) [Field K] [Algebra k K]
    {G D : AffineAlgebraicGroup k} {U : ClosedSubgroup G.val} {p : G.val ⟶ D.val}
    (hU : IsUnipotentRadical U) (hc : GeometricallyConnected U.group.X.hom)
    (hp : IsFppfGroupQuotient U p) (hD : IsSplitTorus D.val) :
    IsUnipotentRadical (G := baseChangedAlgebraicGroup K G) (extendSubgroup K U) := by
  let G' := baseChangedAlgebraicGroup K G
  let D' := baseChangedAlgebraicGroup K D
  let U' := extendSubgroup K U
  let p' := (groupBaseChange k K).map p
  have hp' : IsFppfGroupQuotient (G := G') (Q := D') U' p' := quotientAfterBaseChange K hp
  have hUu : IsUnipotent (closedSubgroupAlgebraicGroup (G := G') U') :=
    (LinearAlgebraicGroups.Unipotent.unipotenceFieldExtension
      (K := K) (closedSubgroupAlgebraicGroup U)).mpr hU.2.2.2.1
  letI := hU.1
  letI := hc
  have hs' : Smooth U'.group.X.hom :=
    inferInstanceAs (Smooth (pullback.snd U.group.X.hom (fieldSpecMap k K)))
  have hc' : GeometricallyConnected U'.group.X.hom :=
    inferInstanceAs (GeometricallyConnected (pullback.snd U.group.X.hom (fieldSpecMap k K)))
  letI := hc'
  haveI := U'.isClosedImmersion
  have hMt := torus_multiplicativeType (D := D') (torus_of_split (splitAfterBaseChange K hD))
  refine ⟨hs', GeometricallyConnected.connectedSpace_of_subsingleton (f := U'.group.X.hom),
    normalOfSchemeKernel hp'.1, hUu, ?_⟩
  intro V hV
  have hv : V.inclusion ≫ p' = 0 :=
    LinearAlgebraicGroups.Unipotent.homFromUnipotentToMultiplicativeType
      (closedSubgroupAlgebraicGroup (G := G') V) D' (V.inclusion ≫ p') hV hMt
  obtain ⟨v, hv⟩ := (schemeKernel_sections hp'.1 V.inclusion.hom.hom).mpr
    (congrArg (fun f : V.group ⟶ D'.val ↦ f.hom.hom) hv)
  letI := isMonHom_of_comp_closed v V.inclusion U'.inclusion hv
  exact ⟨Grp.homMk v, Grp.hom_ext _ _ hv⟩

private theorem fieldSpecSurjective (K : Type u) [Field K] [Algebra k K] :
    Surjective (fieldSpecMap k K) :=
  ⟨fun _ ↦ ⟨IsLocalRing.closedPoint K, Subsingleton.elim _ _⟩⟩

private theorem fieldSpecFlat (K : Type u) [Field K] [Algebra k K] :
    Flat (fieldSpecMap k K) := inferInstance

private theorem baseChangeMapInjective (K : Type u) [Field K] [Algebra k K]
    {X Y : SchemeOver k} {f g : X ⟶ Y}
    (h : (baseChange k K).map f = (baseChange k K).map g) : f = g := by
  let π := pullback.fst X.hom (fieldSpecMap k K)
  letI := fieldSpecSurjective (k := k) K
  letI := fieldSpecFlat (k := k) K
  haveI : Flat π := inferInstanceAs (Flat (pullback.fst X.hom _))
  haveI : Surjective π := inferInstanceAs (Surjective (pullback.fst X.hom _))
  haveI : Epi π := Flat.epi_of_flat_of_surjective _
  apply Over.OverMorphism.ext
  apply (cancel_epi π).mp
  rw [← (baseChangeMapPullback (K := K) f).w, ← (baseChangeMapPullback (K := K) g).w, h]

private theorem geometricSection
    {G D : AffineAlgebraicGroup k} {U : ClosedSubgroup G.val} {p : G.val ⟶ D.val}
    (hU : IsUnipotentRadical U) (hD : IsSplitTorus D.val) (hp : IsFppfGroupQuotient U p)
    (hc : GeometricallyConnected U.group.X.hom) :
    ∃ s : (groupBaseChange k (AlgebraicClosure k)).obj D.val ⟶
      (groupBaseChange k (AlgebraicClosure k)).obj G.val,
      s ≫ (groupBaseChange k (AlgebraicClosure k)).map p = 𝟙 _ := by
  let K := AlgebraicClosure k
  let G' := baseChangedAlgebraicGroup K G
  let D' := baseChangedAlgebraicGroup K D
  let U' := extendSubgroup K U
  let p' := (groupBaseChange k K).map p
  have hp' : IsFppfGroupQuotient (G := G') (Q := D') U' p' := quotientAfterBaseChange K hp
  have hU' : IsUnipotentRadical (G := G') U' := radicalAfterBaseChange K hU hc hp hD
  exact (TorusSections.splitTorusExtension G' D' U' p' hp'.1 hp'.2.1 hp'.2.2.1
    (splitAfterBaseChange K hD) hU'.1 hU'.2.1 hU'.2.2.2.1).1

private theorem geometricMaximalProjection
    {G D : AffineAlgebraicGroup k} {U : ClosedSubgroup G.val} {p : G.val ⟶ D.val}
    (hU : IsUnipotentRadical U) (hD : IsSplitTorus D.val) (hp : IsFppfGroupQuotient U p)
    (hc : GeometricallyConnected U.group.X.hom)
    (T : ClosedSubgroup G.val) (hT : IsGeometricallyMaximalTorus T) :
    IsIso (T.inclusion ≫ p) := by
  obtain ⟨_, _, hmax⟩ := hT
  let K := AlgebraicClosure k
  let F := groupBaseChange k K
  let G' := baseChangedAlgebraicGroup K G
  let D' := baseChangedAlgebraicGroup K D
  let U' := extendSubgroup K U
  let T' := extendSubgroup K T
  let p' := F.map p
  have hp' : IsFppfGroupQuotient (G := G') (Q := D') U' p' := quotientAfterBaseChange K hp
  have hU' : IsUnipotentRadical (G := G') U' := radicalAfterBaseChange K hU hc hp hD
  obtain ⟨s, hs⟩ := geometricSection hU hD hp hc
  have hproj : IsIso (T'.inclusion ≫ p') :=
    iso_projection_of_maximal hp' hU' (splitAfterBaseChange K hD) hs T'
      ((solvable_maximal_torus_iff G' T').mpr hmax)
  haveI : IsIso (F.map (T.inclusion ≫ p)) := by
    rw [F.map_comp]
    change IsIso (T'.inclusion ≫ p')
    exact hproj
  exact baseChangeReflectsIso K (T.inclusion ≫ p)

private theorem splitTorusOfProjection {G D : AffineAlgebraicGroup k}
    {p : G.val ⟶ D.val} (T : ClosedSubgroup G.val) [IsIso (T.inclusion ≫ p)]
    (hD : IsSplitTorus D.val) : IsSplitTorus T.group := by
  obtain ⟨r, ⟨e⟩⟩ := hD
  exact ⟨r, ⟨asIso (T.inclusion ≫ p) ≪≫ e⟩⟩

private theorem maximalSplitOfProjection {G D : AffineAlgebraicGroup k}
    {U : ClosedSubgroup G.val} {p : G.val ⟶ D.val} (hp : IsSchemeKernel p U)
    (hU : IsUnipotent (closedSubgroupAlgebraicGroup U)) (hD : IsSplitTorus D.val)
    (T : ClosedSubgroup G.val) [IsIso (T.inclusion ≫ p)] : IsMaximalSplitTorus T := by
  have hmax := maximal_of_iso_projection hp hU hD T
  exact ⟨splitTorusOfProjection (p := p) T hD, fun S hS hTS ↦ hmax.2 S (torus_of_split hS) hTS⟩

private theorem inclusionOfCentralizes {G : GroupScheme k} {S C V : ClosedSubgroup G}
    (hC : RepresentsSubgroup C (fun _ g ↦ Centralizes S.inclusion g))
    (h : Centralizes S.inclusion V.inclusion.hom.hom) : IsSubgroupOf V C := by
  obtain ⟨v, hv⟩ := (hC _ _).mp h
  letI := C.isClosedImmersion
  letI := isMonHom_of_comp_closed v V.inclusion C.inclusion hv
  exact ⟨Grp.homMk v, Grp.hom_ext _ _ hv⟩

private theorem connectedOfGeometric {X : SchemeOver k}
    (h : GeometricallyConnected X.hom) : ConnectedSpace X.left := by
  letI := h
  exact GeometricallyConnected.connectedSpace_of_subsingleton (f := X.hom)

private theorem geometricSolvable
    {G D : AffineAlgebraicGroup k} {U : ClosedSubgroup G.val} {p : G.val ⟶ D.val}
    [IsAlgClosed k]
    (hs : Smooth G.val.X.hom) (hc : ConnectedSpace G.val.X.left)
    (hU : IsUnipotentRadical U) (hD : IsSplitTorus D.val) (hp : IsFppfGroupQuotient U p) :
    IsSolvable G.val := by
  obtain ⟨hDs, hDc, hDsol⟩ := torus_smooth_connected_solvable D (isTorus_of_split hD)
  letI : Group.IsSolvable (rationalSections U.group) :=
    unipotent_sections_solvable (closedSubgroupAlgebraicGroup U) hU.2.2.2.1
  letI : Group.IsSolvable (rationalSections D.val) :=
    (solvable_iff_sections D hDs hDc).mp hDsol
  exact solvable_of_schemeKernel p hp.1 hs hc

private theorem geometricSolvableSubgroup [IsAlgClosed k] (G : AffineAlgebraicGroup k)
    (hs : Smooth G.val.X.hom) (hc : ConnectedSpace G.val.X.left) (hG : IsSolvable G.val)
    (C : ClosedSubgroup G.val) (hsC : Smooth C.group.X.hom)
    (hcC : ConnectedSpace C.group.X.left) : IsSolvable C.group := by
  letI : Group.IsSolvable (rationalSections G.val) :=
    (solvable_iff_sections G hs hc).mp hG
  letI := mono_over C.inclusion.hom.hom C.isClosedImmersion
  exact (solvable_iff_sections (closedSubgroupAlgebraicGroup C) hsC hcC).mpr
    (Group.isSolvable_of_isSolvable_injective (f := rationalMap C.inclusion)
      (fun _ _ h ↦ (cancel_mono C.inclusion.hom.hom).mp h))

/-- A split subtorus lies in a geometrically maximal torus of the ambient group. -/
private theorem extendSplitTorus
    (existence : Specs.MaximalToriExist.GeometricallyMaximalTorusExists.{u})
    {G D : AffineAlgebraicGroup k} {U : ClosedSubgroup G.val} {p : G.val ⟶ D.val}
    (hsG : Smooth G.val.X.hom) (hcG : GeometricallyConnected G.val.X.hom)
    (hU : IsUnipotentRadical U) (hcU : GeometricallyConnected U.group.X.hom)
    (hp : IsFppfGroupQuotient U p) (hD : IsSplitTorus D.val)
    (S : ClosedSubgroup G.val) (hS : IsSplitTorus S.group) :
    ∃ T : ClosedSubgroup G.val, IsGeometricallyMaximalTorus T ∧ IsSubgroupOf S T := by
  letI := hsG
  letI := connectedOfGeometric hcG
  obtain ⟨C, hC, hsC, hcC⟩ := CocharacterDynamics.connectedTorusCentralizer G S (isTorus_of_split hS)
  let C₀ := closedSubgroupAlgebraicGroup (G := G) C
  obtain ⟨R, hR, _, hRm⟩ := existence C₀ hsC (connectedOfGeometric hcC)
  let T := subgroupOfSubgroup C R
  let K := AlgebraicClosure k
  let F := groupBaseChange k K
  let G' := baseChangedAlgebraicGroup K G
  let D' := baseChangedAlgebraicGroup K D
  let C' := extendSubgroup K C
  let C₁ := closedSubgroupAlgebraicGroup (G := G') C'
  let R' : ClosedSubgroup C₁.val := extendSubgroup K R
  let U' := extendSubgroup K U
  let S' := extendSubgroup K S
  let p' := F.map p
  have hRmax : Specs.GeometricTorusSplitting.IsMaximalTorus (G := C₁) R' :=
    (solvable_maximal_torus_iff C₁ R').mpr hRm
  have hD' : IsSplitTorus D'.val := splitAfterBaseChange K hD
  have hp' : IsFppfGroupQuotient (G := G') (Q := D') U' p' := quotientAfterBaseChange K hp
  have hU' : IsUnipotentRadical (G := G') U' := radicalAfterBaseChange K hU hcU hp hD
  obtain ⟨s, hs⟩ := geometricSection hU hD hp hcU
  obtain ⟨t, ht, hSt⟩ :=
    section_conjugates_lift hp' hU' hs S' (torus_of_split (splitAfterBaseChange K hS))
  let W : ClosedSubgroup G'.val := ⟨D'.val, t, closed_of_section ht⟩
  have hWiso : IsIso (W.inclusion ≫ p') := by
    change IsIso (t ≫ p')
    rw [ht]
    infer_instance
  have hWmax : Specs.GeometricTorusSplitting.IsMaximalTorus (G := G') W :=
    @maximal_of_iso_projection K _ G' D' U' p' hp'.1 hU'.2.2.2.1 hD' W hWiso
  have hWc : IsCommMonObj W.group.X :=
    torus_commutative D' (isTorus_of_split hD')
  obtain ⟨_, hC'⟩ := centralizerSchemeBaseChange k K S.inclusion C hC
  have hC'' : RepresentsSubgroup C' (fun _ g ↦ Centralizes S'.inclusion g) := hC'
  have hWC : IsSubgroupOf W C' := by
    apply inclusionOfCentralizes hC''
    letI := hWc
    apply (centralizes_iff _ _).mpr
    intro X x y
    rw [← hSt]
    change Commute (x ≫ t.hom.hom)
      (y ≫ (S'.inclusion ≫ p').hom.hom ≫ t.hom.hom)
    rw [← Category.assoc y]
    exact (show Commute x (y ≫ (S'.inclusion ≫ p').hom.hom) from
      mul_comm _ _).map (IsMonHom.monoidHom t.hom.hom X)
  obtain ⟨i, hi⟩ := hWC
  let W' : ClosedSubgroup C₁.val := ⟨W.group, i, factor_closed hi⟩
  have hW'max : Specs.GeometricTorusSplitting.IsMaximalTorus (G := C₁) W' := by
    refine ⟨hWmax.1, ?_⟩
    rintro V hV ⟨b, hb⟩
    let V' := subgroupOfSubgroup C' V
    have hWV : IsSubgroupOf W V' := ⟨b, by
      change b ≫ V.inclusion ≫ C'.inclusion = W.inclusion
      rw [← Category.assoc, hb]
      exact hi⟩
    obtain ⟨f, hf⟩ := hWmax.2 V' hV hWV
    refine ⟨f, ?_⟩
    letI := inclusion_mono C'
    apply (cancel_mono C'.inclusion).mp
    rw [Category.assoc, hi]
    exact hf
  have hsG' : Smooth G'.val.X.hom :=
    MorphismProperty.of_isPullback (IsPullback.of_hasPullback _ _) hsG
  have hcG' : ConnectedSpace G'.val.X.left :=
    pullback_of_geometrically hcG.geometrically_connectedSpace K (fieldSpecMap k K)
  have hsC' : Smooth C₁.val.X.hom :=
    MorphismProperty.of_isPullback (IsPullback.of_hasPullback _ _) hsC
  have hcC' : ConnectedSpace C₁.val.X.left :=
    pullback_of_geometrically hcC.geometrically_connectedSpace K (fieldSpecMap k K)
  have hGsol := geometricSolvable hsG' hcG' hU' hD' hp'
  have hCsol := geometricSolvableSubgroup G' hsG' hcG' hGsol C' hsC' hcC'
  obtain ⟨V, _, _, hV, _, _, _⟩ := GeometricTorusSplitting.splitting C₁ hsC' hcC' hCsol
  obtain ⟨a, e, he⟩ := GeometricTorusSplitting.conjugacy C₁ hsC' hcC' hCsol V hV
    W' R' hW'max hRmax
  let aG : 𝟙_ (SchemeOver K) ⟶ G'.val.X := a ≫ V.inclusion.hom.hom ≫ C'.inclusion.hom.hom
  have heG :
      (e.hom ≫ R'.inclusion ≫ C'.inclusion).hom.hom =
        (toUnit W.group.X ≫ aG) * W.inclusion.hom.hom * (toUnit W.group.X ≫ aG)⁻¹ := by
    have eq := congrArg (fun f ↦ f ≫ C'.inclusion.hom.hom) he
    change (e.hom ≫ R'.inclusion).hom.hom ≫ C'.inclusion.hom.hom = _ at eq
    rw [← Category.assoc e.hom R'.inclusion C'.inclusion]
    change (e.hom ≫ R'.inclusion).hom.hom ≫ C'.inclusion.hom.hom = _
    simpa only [aG, Category.assoc, MonObj.mul_comp, GrpObj.inv_comp,
      show W'.inclusion.hom.hom ≫ C'.inclusion.hom.hom = W.inclusion.hom.hom from
        congrArg (fun f : W.group ⟶ G'.val ↦ f.hom.hom) hi] using eq
  have heP : e.hom ≫ (R'.inclusion ≫ C'.inclusion) ≫ p' = W.inclusion ≫ p' := by
    rw [← Category.assoc e.hom (R'.inclusion ≫ C'.inclusion) p']
    apply Grp.hom_ext
    change (e.hom ≫ R'.inclusion ≫ C'.inclusion).hom.hom ≫ p'.hom.hom =
      W.inclusion.hom.hom ≫ p'.hom.hom
    letI : IsCommMonObj (F.obj D.val).X := torus_commutative D' (isTorus_of_split hD')
    rw [heG, MonObj.mul_comp, MonObj.mul_comp, GrpObj.inv_comp]
    rw [mul_comm ((toUnit W.group.X ≫ aG) ≫ p'.hom.hom), mul_inv_cancel_right]
  let T' := extendSubgroup K T
  have hT'eq : T'.inclusion = R'.inclusion ≫ C'.inclusion := by
    change F.map (R.inclusion ≫ C.inclusion) = F.map R.inclusion ≫ F.map C.inclusion
    exact F.map_comp _ _
  have hTiso : IsIso (T'.inclusion ≫ p') := by
    rw [hT'eq]
    haveI : IsIso (e.hom ≫ (R'.inclusion ≫ C'.inclusion) ≫ p') := heP ▸ hWiso
    exact IsIso.of_isIso_comp_left e.hom _
  haveI : IsIso (F.map (T.inclusion ≫ p)) := by
    rw [F.map_comp]
    change IsIso (T'.inclusion ≫ p')
    exact hTiso
  haveI : IsIso (T.inclusion ≫ p) := baseChangeReflectsIso K (T.inclusion ≫ p)
  have hT' : IsMaximalTorus T' := (solvable_maximal_torus_iff G' T').mp
    (@maximal_of_iso_projection K _ G' D' U' p' hp'.1 hU'.2.2.2.1 hD' T' hTiso)
  have haG : Centralizes S'.inclusion aG :=
    (hC'' _ _).mpr ⟨a ≫ V.inclusion.hom.hom, by simp [aG]⟩
  let b : S'.group ⟶ W.group := S'.inclusion ≫ p'
  have hb : b ≫ W.inclusion = S'.inclusion := hSt
  have hbT : (b ≫ e.hom) ≫ T'.inclusion = S'.inclusion := by
    rw [hT'eq, Category.assoc]
    apply Grp.hom_ext
    have eq := congrArg (fun f ↦ b.hom.hom ≫ f) heG
    change (b ≫ e.hom ≫ R'.inclusion ≫ C'.inclusion).hom.hom = _ at eq
    rw [eq, MonObj.comp_mul, MonObj.comp_mul, GrpObj.comp_inv, comp_toUnit_assoc,
      show b.hom.hom ≫ W.inclusion.hom.hom = S'.inclusion.hom.hom from
        congrArg (fun f : S'.group ⟶ G'.val ↦ f.hom.hom) hb]
    have hcomm := ((centralizes_iff _ _).mp haG S'.group.X (toUnit _) (𝟙 _)).eq
    simp only [Category.id_comp] at hcomm
    exact mul_inv_eq_iff_eq_mul.mpr hcomm
  let j := (S.inclusion ≫ p) ≫ inv (T.inclusion ≫ p)
  refine ⟨T, ⟨hR, T'.isClosedImmersion, hT'⟩, j, ?_⟩
  apply Grp.hom_ext
  apply baseChangeMapInjective K
  change (F.map (j ≫ T.inclusion)).hom.hom = S'.inclusion.hom.hom
  rw [F.map_comp]
  have hj : F.map j = b ≫ e.hom := by
    apply (cancel_mono (T'.inclusion ≫ p')).mp
    calc
      F.map j ≫ (T'.inclusion ≫ p') = F.map (j ≫ (T.inclusion ≫ p)) := by
        change F.map j ≫ (F.map T.inclusion ≫ F.map p) = _
        simp only [Functor.map_comp]
      _ = F.map (S.inclusion ≫ p) := by simp [j]
      _ = (b ≫ e.hom) ≫ (T'.inclusion ≫ p') := by
        rw [← Category.assoc, hbT, Functor.map_comp]
        rfl
  rw [hj]
  exact congrArg (fun f : S'.group ⟶ G'.val ↦ f.hom.hom) hbT

private theorem maximalSplitProjection
    {G D : AffineAlgebraicGroup k} {p : G.val ⟶ D.val} (hD : IsSplitTorus D.val)
    (hproj : ∀ T : ClosedSubgroup G.val, IsGeometricallyMaximalTorus T → IsIso (T.inclusion ≫ p))
    (hext : ∀ S : ClosedSubgroup G.val, IsSplitTorus S.group →
      ∃ T : ClosedSubgroup G.val, IsGeometricallyMaximalTorus T ∧ IsSubgroupOf S T)
    (T : ClosedSubgroup G.val) (hT : IsMaximalSplitTorus T) :
    IsIso (T.inclusion ≫ p) := by
  obtain ⟨V, hV, hTV⟩ := hext T hT.1
  letI := hproj V hV
  obtain ⟨e, he⟩ := subgroupOf_mutual_iso hTV (hT.2 V (splitTorusOfProjection (p := p) V hD) hTV)
  rw [← he, Category.assoc]
  infer_instance

theorem splitting_conditional
    (existence : Specs.MaximalToriExist.GeometricallyMaximalTorusExists.{u}) :
    Specs.SplitTorusConjugacy.Splitting.{u} := by
  intro k _ G hG
  obtain ⟨U, D, p, hU, hcU, hp, hD⟩ := diagonalQuotient G hG
  obtain ⟨hsG, hcG⟩ := splitSolvableGeometry hG G.property
  have hproj := geometricMaximalProjection hU hD hp hcU
  have hext := extendSplitTorus existence hsG hcG hU hcU hp hD
  have hmax (T : ClosedSubgroup G.val) : IsMaximalSplitTorus T ↔ IsIso (T.inclusion ≫ p) := by
    exact ⟨maximalSplitProjection hD hproj hext T,
      fun h ↦ @maximalSplitOfProjection k _ G D U p hp.1 hU.2.2.2.1 hD T h⟩
  obtain ⟨T, hT⟩ := existence G hsG (connectedOfGeometric hcG)
  exact ⟨U, D, p, hU, hp, hD, ⟨T, (hmax T).mpr (hproj T hT)⟩,
    fun V ↦ ⟨hmax V, fun h ↦ @product_isIso k _ G D U V p hp.1 ((hmax V).mp h)⟩,
    hproj, hext⟩

private def Conjugates {G H : GroupScheme k} (i j : H ⟶ G)
    {X : SchemeOver k} (g : X ⟶ G.X) : Prop :=
  conjugateFamily i g = fst H.X X ≫ j.hom.hom

private theorem conjugates_iff {G H : GroupScheme k} (i j : H ⟶ G)
    {X : SchemeOver k} (g : X ⟶ G.X) :
    Conjugates i j g ↔
      ∀ (Y : SchemeOver k) (y : Y ⟶ X) (t : Y ⟶ H.X),
        (y ≫ g) * (t ≫ i.hom.hom) * (y ≫ g)⁻¹ = t ≫ j.hom.hom := by
  constructor
  · intro h Y y t
    simpa only [comp_conjugateFamily, lift_fst_assoc, lift_snd_assoc] using
      congrArg (fun f ↦ lift t y ≫ f) h
  · intro h
    exact h _ (snd H.X X) (fst H.X X)

private theorem conjugatesBaseChange (K : Type u) [Field K] [Algebra k K]
    {G H : GroupScheme k} (i j : H ⟶ G) {X : SchemeOver K}
    (g : X ⟶ ((groupBaseChange k K).obj G).X) :
    Conjugates ((groupBaseChange k K).map i) ((groupBaseChange k K).map j) g ↔
      Conjugates i j (((extensionAdj (k := k) K).homEquiv X G.X).symm g) := by
  let F := baseChange k K
  let L := Over.map (fieldSpecMap k K)
  let adj := extensionAdj (k := k) K
  let b := lift (L.map (fst (F.obj H.X) X) ≫ adj.counit.app H.X) (L.map (snd (F.obj H.X) X))
  have : IsIso b := isIso_over_product_map (fieldSpecMap k K) H.X X
  let g' : X ⟶ F.obj G.X := g
  let q : H.X ⊗ G.X ⟶ G.X := fst H.X G.X ≫ j.hom.hom
  have eq : (prodComparisonIso F H.X G.X).inv ≫ F.map q =
      fst (F.obj H.X) (F.obj G.X) ≫ F.map j.hom.hom := by
    rw [Functor.map_comp, ← Category.assoc, prodComparison_inv_fst]
  have eg : conjugateFamily ((groupBaseChange k K).map i) g =
      (F.obj H.X ◁ g') ≫ (prodComparisonIso F H.X G.X).inv ≫ F.map (conjugation i) := by
    rw [conjugation_baseChange K i]
    exact (whisker_conjugation ((groupBaseChange k K).map i) g).symm
  change conjugateFamily ((groupBaseChange k K).map i) g =
    fst (F.obj H.X) X ≫ F.map j.hom.hom ↔ _
  change _ = fst (F.obj H.X) X ≫ F.map j.hom.hom ↔
    Conjugates i j ((adj.homEquiv X G.X).symm g')
  rw [eg, ← whiskerLeft_fst_assoc (F.obj H.X) g', ← eq,
    ← (adj.homEquiv (F.obj H.X ⊗ X) G.X).symm.injective.eq_iff]
  erw [adjoint_family K (conjugation i) g', adjoint_family K q g']
  change b ≫ _ = b ≫ _ ↔ _
  rw [cancel_epi, whisker_conjugation]
  simp only [Conjugates, q, whiskerLeft_fst_assoc]
  rfl

private theorem conjugatorLocus {G H : GroupScheme k} (i j : H ⟶ G) {M : SchemeOver k}
    [IsAffine H.X.left] [IsAffine M.left] [IsSeparated G.X.hom] (s : M ⟶ G.X) :
    ∃ (Y : SchemeOver k) (l : Y ⟶ M), IsClosedImmersion l.left ∧
      ∀ (X : SchemeOver k) (x : X ⟶ M),
        Conjugates i j (x ≫ s) ↔ ∃ y : X ⟶ Y, y ≫ l = x := by
  let f := conjugateFamily i s
  let g := fst H.X M ≫ j.hom.hom
  let d := equalizer.ι f g
  obtain ⟨Y, l, hl, hY⟩ := familyFactorizationLocus d (inferInstanceAs (IsClosedImmersion d.left))
  refine ⟨Y, l, hl, fun X x ↦ ?_⟩
  rw [← hY]
  change conjugateFamily i (x ≫ s) = _ ↔ _
  have hf : (H.X ◁ x) ≫ f = conjugateFamily i (x ≫ s) := by
    rw [comp_conjugateFamily]
    simp only [conjugateFamily, whiskerLeft_fst_assoc, whiskerLeft_snd_assoc]
  rw [← hf, ← whiskerLeft_fst_assoc H.X x]
  exact ⟨fun h ↦ ⟨equalizer.lift _ h, equalizer.lift_ι _ _⟩, fun ⟨y, hy⟩ ↦ by
    rw [← hy, Category.assoc, Category.assoc, equalizer.condition]⟩

private theorem centralizerOnSchemes {G H U : GroupScheme k}
    (i : H ⟶ G) (inc : U ⟶ G) (Z : ClosedSubgroup U)
    (hZ : ∀ (R : TestAlgebra k) (x : Points U.X R), Centralizes i (x ≫ inc.hom.hom) ↔
      ∃ y : Points Z.group.X R, y ≫ Z.inclusion.hom.hom = x)
    {X : SchemeOver k} (x : X ⟶ U.X) :
    Centralizes i (x ≫ inc.hom.hom) ↔
      ∃ y : X ⟶ Z.group.X, y ≫ Z.inclusion.hom.hom = x := by
  have := Z.isClosedImmersion
  let C := X.left.affineOpenCover.openCover
  constructor
  · intro hx
    apply (factorsThrough_iff_cover C Z.inclusion.hom.hom x).mpr
    intro a
    let W := overCoverObj C a
    let f := overCoverMap C a
    have hW : IsAffine W.left := inferInstanceAs (IsAffine (Spec (X.left.affineOpenCover.X a)))
    obtain ⟨R, ⟨e⟩⟩ := (essImage_algSpec (R := CommRingCat.of k)).mpr hW
    obtain ⟨b, hb⟩ := (hZ R.unop (e.hom ≫ f ≫ x)).mp (by
      apply (centralizes_iff _ _).mpr
      intro B y t
      simpa only [Category.assoc] using
        (centralizes_iff _ _).mp hx B (y ≫ e.hom ≫ f) t)
    exact ⟨e.inv ≫ b, by simp only [Category.assoc, hb, Iso.inv_hom_id_assoc, f]⟩
  · rintro ⟨y, rfl⟩
    have hZinc : Centralizes i (Z.inclusion.hom.hom ≫ inc.hom.hom) := by
      apply (centralizes_iff _ _).mpr
      intro B v t
      -- The conjugation identity can be checked on an affine open cover of the test scheme.
      let D := B.left.affineOpenCover.openCover
      apply Over.OverMorphism.ext
      apply D.hom_ext
      intro a
      let W := overCoverObj D a
      let f := overCoverMap D a
      have hW : IsAffine W.left := inferInstanceAs (IsAffine (Spec (B.left.affineOpenCover.X a)))
      obtain ⟨R, ⟨e⟩⟩ := (essImage_algSpec (R := CommRingCat.of k)).mpr hW
      have hx := (hZ R.unop ((e.hom ≫ f ≫ v) ≫ Z.inclusion.hom.hom)).mpr ⟨_, rfl⟩
      have hc := ((centralizes_iff _ _).mp hx _ (𝟙 _) (e.hom ≫ f ≫ t)).eq
      have heq := congrArg (e.inv ≫ ·) hc
      change (f ≫ ((v ≫ Z.inclusion.hom.hom ≫ inc.hom.hom) * (t ≫ i.hom.hom))).left =
        (f ≫ ((t ≫ i.hom.hom) * (v ≫ Z.inclusion.hom.hom ≫ inc.hom.hom))).left
      simpa only [MonObj.comp_mul, Category.assoc, Category.id_comp, Iso.inv_hom_id_assoc]
        using congrArg (fun m ↦ m.left) heq
    apply (centralizes_iff _ _).mpr
    intro B v t
    simpa only [Category.assoc] using (centralizes_iff _ _).mp hZinc B (v ≫ y) t

private theorem geometricConjugator
    {G D : AffineAlgebraicGroup k} {U : ClosedSubgroup G.val} {p : G.val ⟶ D.val}
    (hU : IsUnipotentRadical U) (hcU : GeometricallyConnected U.group.X.hom)
    (hp : IsFppfGroupQuotient U p) (hD : IsSplitTorus D.val)
    (T₁ T₂ : ClosedSubgroup G.val) [IsIso (T₁.inclusion ≫ p)] [IsIso (T₂.inclusion ≫ p)] :
    let K := AlgebraicClosure k
    let F := groupBaseChange k K
    let e := asIso (T₁.inclusion ≫ p) ≪≫ (asIso (T₂.inclusion ≫ p)).symm
    ∃ a : 𝟙_ (SchemeOver K) ⟶ (F.obj U.group).X,
      Conjugates (F.map T₁.inclusion) (F.map (e.hom ≫ T₂.inclusion))
        (a ≫ (F.map U.inclusion).hom.hom) := by
  dsimp only
  let K := AlgebraicClosure k
  let F := groupBaseChange k K
  let G' := baseChangedAlgebraicGroup K G
  let D' := baseChangedAlgebraicGroup K D
  let U' := extendSubgroup K U
  let p' := F.map p
  let e₁ := asIso (T₁.inclusion ≫ p)
  let e₂ := asIso (T₂.inclusion ≫ p)
  let s₁ := e₁.inv ≫ T₁.inclusion
  let s₂ := e₂.inv ≫ T₂.inclusion
  have hs₁ : s₁ ≫ p = 𝟙 D.val := by
    rw [show s₁ = e₁.inv ≫ T₁.inclusion from rfl, Category.assoc]
    exact e₁.inv_hom_id
  have hs₂ : s₂ ≫ p = 𝟙 D.val := by
    rw [show s₂ = e₂.inv ≫ T₂.inclusion from rfl, Category.assoc]
    exact e₂.inv_hom_id
  have hs₁' : F.map s₁ ≫ p' = 𝟙 _ := by rw [← F.map_comp, hs₁, F.map_id]
  have hs₂' : F.map s₂ ≫ p' = 𝟙 _ := by rw [← F.map_comp, hs₂, F.map_id]
  have hp' : IsFppfGroupQuotient (G := G') (Q := D') U' p' := quotientAfterBaseChange K hp
  have hU' := radicalAfterBaseChange K hU hcU hp hD
  obtain ⟨a, ha⟩ := (TorusSections.splitTorusExtension G' D' U' p' hp'.1 hp'.2.1 hp'.2.2.1
    (splitAfterBaseChange K hD) hU'.1 hU'.2.1 hU'.2.2.2.1).2
    (F.map s₁) (F.map s₂) hs₁' hs₂'
  refine ⟨a, (conjugates_iff _ _ _).mpr ?_⟩
  intro X x t
  let q : X ⟶ D'.val.X := t ≫ (F.map e₁.hom).hom.hom
  have h₁ : F.map e₁.hom ≫ F.map s₁ = F.map T₁.inclusion := by
    rw [← F.map_comp]
    simp [s₁]
  have h₂ : F.map e₁.hom ≫ F.map s₂ = F.map ((e₁ ≪≫ e₂.symm).hom ≫ T₂.inclusion) := by
    rw [← F.map_comp]
    simp [s₂]
  have h₁X : (F.map e₁.hom).hom.hom ≫ (F.map s₁).hom.hom = (F.map T₁.inclusion).hom.hom :=
    congrArg (fun f ↦ f.hom.hom) h₁
  have h₂X : (F.map e₁.hom).hom.hom ≫ (F.map s₂).hom.hom =
      (F.map ((e₁ ≪≫ e₂.symm).hom ≫ T₂.inclusion)).hom.hom :=
    congrArg (fun f ↦ f.hom.hom) h₂
  let c : D'.val.X ⟶ G'.val.X := toUnit D'.val.X ≫ a ≫ U'.inclusion.hom.hom
  let f₁ : D'.val.X ⟶ G'.val.X := (F.map s₁).hom.hom
  have eq := congrArg (fun m ↦ q ≫ m) ha
  change q ≫ (F.map s₂).hom.hom = q ≫ (c * f₁ * c⁻¹) at eq
  simp only [MonObj.comp_mul, GrpObj.comp_inv, c, f₁, comp_toUnit_assoc] at eq
  have hx : x = toUnit X := toUnit_unique _ _
  rw [hx]
  change (toUnit X ≫ a ≫ U'.inclusion.hom.hom) * (t ≫ (F.map T₁.inclusion).hom.hom) *
    (toUnit X ≫ a ≫ U'.inclusion.hom.hom)⁻¹ =
      t ≫ (F.map ((e₁ ≪≫ e₂.symm).hom ≫ T₂.inclusion)).hom.hom
  simpa only [q, Category.assoc, h₁X, h₂X] using eq.symm

/-- A normalized conjugator is unique over every test scheme, and its closed
locus has a geometric point. Hence the locus is the ground field itself. -/
private theorem descendConjugator
    {G U : AffineAlgebraicGroup k} {H : GroupScheme k} (i j : H ⟶ G.val)
    (hH : IsAffine H.X.left) (inc : U.val ⟶ G.val) (N P Z : ClosedSubgroup U.val)
    (htriple : IsIso (Specs.TorusLimitFactorization.tripleProduct N P Z))
    (hZ : ∀ (R : TestAlgebra k) (x : Points U.val.X R),
      Centralizes i (x ≫ inc.hom.hom) ↔
        ∃ y : Points Z.group.X R, y ≫ Z.inclusion.hom.hom = x)
    (geometric :
      let K := AlgebraicClosure k
      let F := groupBaseChange k K
      ∃ a : 𝟙_ (SchemeOver K) ⟶ (F.obj U.val).X,
        Conjugates (F.map i) (F.map j) (a ≫ (F.map inc).hom.hom)) :
    ∃ a : 𝟙_ (SchemeOver k) ⟶ U.val.X, Conjugates i j (a ≫ inc.hom.hom) := by
  let J := inc.hom.hom
  let M := N.group.X ⊗ P.group.X
  let m := Specs.TorusLimitFactorization.tripleProduct N P Z
  let s := Specs.TorusLimitFactorization.pairProduct N P
  let z := Z.inclusion.hom.hom
  haveI : IsIso m := htriple
  have homFormula {X : SchemeOver k} (x : X ⟶ M) (b : X ⟶ Z.group.X) :
      lift x b ≫ m = (x ≫ s) * (b ≫ z) := by
    simp only [m, Specs.TorusLimitFactorization.tripleProduct, MonObj.comp_mul]
    exact congrArg₂ (· * ·)
      (by simpa only [Category.assoc, s] using congrArg (· ≫ s) (lift_fst x b))
      (by simpa only [Category.assoc, z] using congrArg (· ≫ z) (lift_snd x b))
  have hz {X : SchemeOver k} (x : X ⟶ U.val.X) :
      Centralizes i (x ≫ J) ↔ ∃ b : X ⟶ Z.group.X, b ≫ z = x :=
    centralizerOnSchemes i inc Z hZ x
  letI := G.property.1
  letI : IsSeparated G.val.X.hom := IsSeparated.of_isAffineHom _
  letI := hH
  letI : IsAffine N.group.X.left := (closedSubgroupAlgebraicGroup (G := U) N).property.1
  letI : IsAffine P.group.X.left := (closedSubgroupAlgebraicGroup (G := U) P).property.1
  letI : IsAffine M.left := affine_tensor
  obtain ⟨Y, l, hl, hY⟩ := conjugatorLocus i j (s ≫ J)
  letI : Mono l := mono_over l hl
  have unique {X : SchemeOver k} (x y : X ⟶ M)
      (hx : Conjugates i j (x ≫ s ≫ J)) (hy : Conjugates i j (y ≫ s ≫ J)) : x = y := by
    let d := (x ≫ s)⁻¹ * (y ≫ s)
    have hcentral : Centralizes i (d ≫ J) := by
      apply (centralizes_iff _ _).mpr
      intro B b t
      have h₁ := (conjugates_iff _ _ _).mp hx B b t
      have h₂ := (conjugates_iff _ _ _).mp hy B b t
      apply mul_inv_eq_iff_eq_mul.mp
      simp only [d, MonObj.mul_comp, MonObj.comp_mul, GrpObj.inv_comp, GrpObj.comp_inv,
        Category.assoc]
      calc
        (b ≫ x ≫ s ≫ J)⁻¹ * (b ≫ y ≫ s ≫ J) * (t ≫ i.hom.hom) *
            ((b ≫ x ≫ s ≫ J)⁻¹ * (b ≫ y ≫ s ≫ J))⁻¹ =
            (b ≫ x ≫ s ≫ J)⁻¹ * (t ≫ j.hom.hom) * (b ≫ x ≫ s ≫ J) := by
              rw [← h₂]
              group
        _ = t ≫ i.hom.hom := by rw [← h₁]; group
    obtain ⟨b, hb⟩ := hz d |>.mp hcentral
    have hm : lift x b ≫ m = lift y (1 : X ⟶ Z.group.X) ≫ m := by
      rw [homFormula, homFormula, hb, MonObj.one_comp, mul_one]
      exact mul_inv_cancel_left _ _
    have e := congrArg (fun f ↦ f ≫ fst M Z.group.X) ((cancel_mono m).mp hm)
    simpa only [lift_fst] using e
  have subterminal {X : SchemeOver k} (x y : X ⟶ Y) : x = y := by
    apply (cancel_mono l).mp
    exact unique (x ≫ l) (y ≫ l)
      ((hY X _).mpr ⟨x, rfl⟩) ((hY X _).mpr ⟨y, rfl⟩)
  let K := AlgebraicClosure k
  let L := Over.map (fieldSpecMap k K)
  let adj := extensionAdj (k := k) K
  let X := L.obj (𝟙_ (SchemeOver K))
  obtain ⟨a, ha⟩ := geometric
  let b : X ⟶ U.val.X := (adj.homEquiv _ _).symm a
  have hb : Conjugates i j (b ≫ J) := by
    rw [← adj.homEquiv_naturality_right_symm]
    exact (conjugatesBaseChange K i j _).mp ha
  let x : X ⟶ M := b ≫ inv m ≫ fst M Z.group.X
  let c : X ⟶ Z.group.X := b ≫ inv m ≫ snd M Z.group.X
  have hdecomp : b = (x ≫ s) * (c ≫ z) := by
    rw [← homFormula]
    have h : lift x c = b ≫ inv m := by apply hom_ext <;> simp [x, c]
    simp [h]
  have hn : Conjugates i j (x ≫ s ≫ J) := by
    apply (conjugates_iff _ _ _).mpr
    intro B f t
    have h := (conjugates_iff _ _ _).mp hb B f t
    have hc := (centralizes_iff _ _).mp ((hz (c ≫ z)).mpr ⟨c, rfl⟩) B f t
    simp only [Category.assoc] at hc
    rw [hdecomp] at h
    simp only [Category.assoc, MonObj.mul_comp, MonObj.comp_mul] at h
    let a := f ≫ x ≫ s ≫ J
    let d := f ≫ c ≫ z ≫ J
    let v := t ≫ i.hom.hom
    change (a * d) * v * (a * d)⁻¹ = t ≫ j.hom.hom at h
    change a * v * a⁻¹ = _
    calc
      a * v * a⁻¹ = (a * d) * v * (a * d)⁻¹ := by
        have hcomm : d * v = v * d := hc.eq
        rw [mul_inv_rev, mul_assoc a d v, hcomm]
        group
      _ = _ := h
  obtain ⟨y, _⟩ := (hY X x).mp hn
  haveI : Mono Y.hom := ⟨fun {_} f g h ↦ by
    let B' : SchemeOver k := Over.mk (f ≫ Y.hom)
    let f' : B' ⟶ Y := Over.homMk f rfl
    let g' : B' ⟶ Y := Over.homMk g h.symm
    exact congrArg (fun r ↦ r.left) (subterminal f' g')⟩
  haveI : Surjective Y.hom :=
    ⟨fun _ ↦ ⟨y.left (IsLocalRing.closedPoint K), Subsingleton.elim _ _⟩⟩
  letI := hl
  letI : IsAffine Y.left := isAffine_of_isAffineHom l.left
  haveI : IsIso Y.hom := Flat.isIso_of_surjective_of_mono _
  let y₀ : 𝟙_ (SchemeOver k) ⟶ Y := Over.homMk (inv Y.hom) (IsIso.inv_hom_id _)
  refine ⟨(y₀ ≫ l) ≫ s, ?_⟩
  simpa only [Category.assoc] using
    (hY (𝟙_ (SchemeOver k)) (y₀ ≫ l)).mpr ⟨y₀, rfl⟩

private theorem rationalConjugator
    {G D : AffineAlgebraicGroup k} {U : ClosedSubgroup G.val} {p : G.val ⟶ D.val}
    (hG : IsSplitSolvable G.val) (hU : IsUnipotentRadical U)
    (hcU : GeometricallyConnected U.group.X.hom)
    (hp : IsFppfGroupQuotient U p) (hD : IsSplitTorus D.val)
    (T₁ T₂ : ClosedSubgroup G.val) [IsIso (T₁.inclusion ≫ p)] [IsIso (T₂.inclusion ≫ p)] :
    let e := asIso (T₁.inclusion ≫ p) ≪≫ (asIso (T₂.inclusion ≫ p)).symm
    ∃ a : 𝟙_ (SchemeOver k) ⟶ U.group.X,
      Conjugates T₁.inclusion (e.hom ≫ T₂.inclusion) (a ≫ U.inclusion.hom.hom) := by
  dsimp only
  let e := asIso (T₁.inclusion ≫ p) ≪≫ (asIso (T₂.inclusion ≫ p)).symm
  let i := T₁.inclusion
  let j := e.hom ≫ T₂.inclusion
  obtain ⟨_, _, _, _, _, _, _, _, N, P, Z, _, _, _, _, _, hpts, htriple, _⟩ :=
    TorusLimitFactorization.factorization G D p U T₁ hG ((splitTorus_iff_points D).mp hD)
      hp.1 hU.1 hcU hU.2.2.1
      ((splitTorus_iff_points (closedSubgroupAlgebraicGroup T₁)).mp (splitTorusOfProjection (p := p) T₁ hD))
      inferInstance hU.2.2.2.1 hU.2.2.2.2
  exact descendConjugator i j (closedSubgroupAlgebraicGroup T₁).property.1
    (U := closedSubgroupAlgebraicGroup U) U.inclusion N P Z htriple
    (fun R x ↦ (hpts R x).2.2.2.2) (geometricConjugator hU hcU hp hD T₁ T₂)

theorem conjugacy_conditional
    (existence : Specs.MaximalToriExist.GeometricallyMaximalTorusExists.{u}) :
    Specs.SplitTorusConjugacy.Conjugacy.{u} := by
  intro k _ G hG U hU T₁ T₂ h₁ h₂
  obtain ⟨V, D, p, hV, hcV, hp, hD⟩ := diagonalQuotient G hG
  obtain ⟨hsG, hcG⟩ := splitSolvableGeometry hG G.property
  have projection := maximalSplitProjection hD
    (geometricMaximalProjection hV hD hp hcV)
    (extendSplitTorus existence hsG hcG hV hcV hp hD)
  letI := projection T₁ h₁
  letI := projection T₂ h₂
  obtain ⟨a, ha⟩ := rationalConjugator hG hV hcV hp hD T₁ T₂
  obtain ⟨v, hv⟩ := hU.2.2.2.2 V hV.2.2.2.1
  let e := asIso (T₁.inclusion ≫ p) ≪≫ (asIso (T₂.inclusion ≫ p)).symm
  refine ⟨a ≫ v.hom.hom, e, ?_⟩
  have hv' : v.hom.hom ≫ U.inclusion.hom.hom = V.inclusion.hom.hom :=
    congrArg (fun f : V.group ⟶ G.val ↦ f.hom.hom) hv
  dsimp only
  rw [Category.assoc a, hv']
  have eq := (conjugates_iff _ _ _).mp ha T₁.group.X (toUnit _) (𝟙 _)
  simpa only [Category.id_comp, e] using eq.symm

end
end LinearAlgebraicGroups.SplitTorusConjugacy

universe v8_closure_337408f07d18d214_u0
theorem _root_.«LinearAlgebraicGroups».«SplitTorusConjugacy».«conjugacy» : _root_.«LinearAlgebraicGroups».«Specs».«SplitTorusConjugacy».«Conjugacy».{v8_closure_337408f07d18d214_u0} :=
  @_root_.«LinearAlgebraicGroups».«SplitTorusConjugacy».«conjugacy_conditional».{v8_closure_337408f07d18d214_u0} (@_root_.«LinearAlgebraicGroups».«MaximalToriExist».«geometricallyMaximalTorusExists».{v8_closure_337408f07d18d214_u0})
theorem _root_.«LinearAlgebraicGroups».«SplitTorusConjugacy».«splitting» : _root_.«LinearAlgebraicGroups».«Specs».«SplitTorusConjugacy».«Splitting».{v8_closure_337408f07d18d214_u0} :=
  @_root_.«LinearAlgebraicGroups».«SplitTorusConjugacy».«splitting_conditional».{v8_closure_337408f07d18d214_u0} (@_root_.«LinearAlgebraicGroups».«MaximalToriExist».«geometricallyMaximalTorusExists».{v8_closure_337408f07d18d214_u0})
