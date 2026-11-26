import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Relative.ReductiveLieCentralizers
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Reductive.SemisimpleLieCentralizer
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Reductive.TorusFreeUnipotent
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.RootData.CharacterPairing
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Affine.Components
import Batteries.Tactic.OpenPrivate
import Mathlib.Tactic.Group

import Mathlib.LinearAlgebra.Eigenspace.Minpoly
import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic

import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.RootData.RankOneFlag
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.RootData.RootGroups
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite WithConv
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj TensorProduct

universe u

namespace LinearAlgebraicGroups.Relative.ReductiveLieCentralizers

open LinearAlgebraicGroups.Specs
open Specs.Relative.ReductiveLieCentralizers
open Specs.GeometricBorelConjugacy (IsReducedIdentityComponent subgroupOfSubgroup)
open Specs.GeometricRadicals
  (GeometricGroup IsMaximalTorus IsReductive IsSmoothConnectedNormal IsSplitTorus IsTorus
    IsTrivialSubgroup baseChangedSubgroup geometricUnipotentRadical)
open Specs.SchemeDerivedGroup (IsSubgroupOf)
open Specs.Unipotent (IsUnipotent baseChangedAlgebraicGroup closedSubgroupAlgebraicGroup)
open Specs.AdjointRepresentation (GroupPoints constants dualMap scale)
open Specs.SemisimpleLieCentralizer (GeometricallySemisimple)
open Specs.CharacterDescent (Character Cocharacter)
open Specs.CharacterPairing (absoluteRoots adjointWeightVectors characterValue)
open Specs.RankOneFlag (Centralizer SameSubgroup)
open Specs.RootGroups (IsRootSubgroup)
open Specs.EquivariantUnipotentSeries (AutomorphismAction IsStable onPoints)
open EquivariantUnipotentSeries (pointAction)
open Specs.DiagonalizableGroups (IntegerCharacters groupAlgebra integerGenerator)
open CocharacterDynamics (LimitDecomposition oppositeCocharacter bigCellMap multiplyFactors)

open private isReduced_of_smooth_over_field
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Affine.SmoothnessCriteria

open private subgroupOf_trans factor_group_through_subgroup
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Reductive.GeometricBorelConjugacy
open private group_irreducible_of_connected
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Reductive.CocharacterOpenCell
open private factors_of_range_subset from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Reductive.SubtorusCentralizer

open private baseChangeMapIsPullback from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Flag.HomogeneousQuotient
open private normalSubgroup_of_iso from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Flag.NormalAffineQuotient
open private inclusion_mono isTorus_iff_coordinates
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Reductive.MaximalToriConjugate
open private split_of_torus from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Solvable.GeometricTorusSplitting
open private unipotent_iso from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Reductive.TorusFreeUnipotent
open private torus_baseChange_algClosure from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Reductive.SubtorusCentralizer

open private mono_over from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Affine.Stabilizers
open private closedSeries_inclusion_closed isIso_of_trivial_kernel
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Unipotent.PerfectFieldSplitness
open private action_character actionValue
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Solvable.EquivariantUnipotentSeries
open private toMultiplicativeGroup_points pointsIso_spec integerPointsIso
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Multiplicative.DiagonalizableGroups
open private centralizes_iff_affine from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Reductive.ConnectedTorusCentralizer
open private torus_smooth_connected_solvable
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Reductive.GeometricBorelConjugacy
open private torus_multiplicativeType from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Solvable.GeometricTorusSplitting
open private ReducedIdentityComponent.factorHom
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Solvable.EquivariantUnipotentSeries
open private factor_closed from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Reductive.GeometricRadicals
open private characterValue_one
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.RootData.CharacterPairing

open private onPoints_injective onPoints_comp from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Unipotent.CentralSeries
open private matrixPointMap matrixDual matrixDual_kernel from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Affine.LieBracket

open Specs.Unipotent (Index)
open Specs.SemisimpleLieCentralizer (InvariantDerivation matrixAction)
open private tangentComparison tangentComparison_matrix universalMatrix_coaction
  coactionOperator coactionOperator_matrix from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Reductive.SemisimpleLieCentralizer
open private splitPresentation zeroWeightVectors_iff_centralizes canonicalZero_eq
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.RootData.CharacterPairing
open private isFixedBy_conjugation_iff from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Reductive.DiagonalizableFixedLocus
open private local_maximal_of_ambient solvable_maximal_torus_iff
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Reductive.MaximalToriConjugate
open private matrixDifferential_eq matrixCoefficient_add matrixDifferential_injective
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Affine.LieBracket
open private sections_factor_of_affine from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Unipotent.PerfectFieldSplitness
open private factors_reduced_component from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Reductive.SubtorusCentralizer
open private torus_commutative from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Reductive.TorusFreeUnipotent
open private isAffine_baseChange from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Affine.IdentityTangent

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 900000
set_option synthInstance.maxHeartbeats 90000
set_option linter.style.haveILetI false

variable {k : Type u} [Field k]

private theorem smoothIdentityComponent (C : AffineAlgebraicGroup k) (hs : Smooth C.val.X.hom) :
    ∃ H : ClosedSubgroup C.val, IsReducedIdentityComponent H ∧
      IsOpenImmersion H.inclusion.hom.hom.left ∧ Smooth H.group.X.hom ∧
      GeometricallyConnected H.group.X.hom := by
  obtain ⟨Q, H, q, i, hi, _, _, _⟩ := identityComponentAndQuotient k C
  have hSmooth : Smooth H.X.hom := by
    rw [← Over.w i.hom.hom]
    letI := hi.openImmersion
    letI := hs
    infer_instance
  letI := hSmooth
  refine ⟨⟨H, i, hi.closedImmersion⟩, ⟨isReduced_of_smooth_over_field H.X.hom, ?_⟩,
    hi.openImmersion, hSmooth, hi.geometricallyConnected⟩
  exact hi.identityComponent.trans (congrArg (fun x => connectedComponent (η[C.val.X].left x))
    (Subsingleton.elim (α := PrimeSpectrum k) _ _))

private theorem smoothCentralizerComponent
    (G : AffineAlgebraicGroup k) (hs : Smooth G.val.X.hom)
    {I : Type u} [Fintype I] [DecidableEq I] (L : AffineGroupCategory k)
    (l : (groupPointsFunctor k).obj L.val ≅ StandardGroups.generalLinearPoints k I)
    (f : G.val ⟶ L.val) (hf : IsClosedImmersion f.hom.hom.left) (y : Lie k G.val)
    (hy : GeometricallySemisimple (InfinitesimalCommutator.matrixDifferential f l y)) :
    ∃ C : ClosedSubgroup G.val,
      IsMatrixCentralizer l f (InfinitesimalCommutator.matrixDifferential f l y) C ∧
      Smooth C.group.X.hom ∧
      ∃ H : ClosedSubgroup C.group, IsReducedIdentityComponent H ∧
        IsOpenImmersion H.inclusion.hom.hom.left ∧ Smooth H.group.X.hom ∧
        GeometricallyConnected H.group.X.hom := by
  obtain ⟨C, hsC, hC, _, _⟩ := SemisimpleLieCentralizer.schemeCentralizerOfSemisimple
    k G L (identityLieStructure G) hs I l f hf y hy
  exact ⟨C, hC, hsC, smoothIdentityComponent (closedSubgroupAlgebraicGroup C) hsC⟩

private theorem containsRankOneCentralizer [IsAlgClosed k]
    (G : AffineAlgebraicGroup k) (H T : ClosedSubgroup G.val)
    (hTH : IsSubgroupOf T H) {α : Character T.group} (C : Centralizer T α)
    (hC : IsReductive (closedSubgroupAlgebraicGroup C.subgroup))
    {lambdaT : Cocharacter T.group}
    (D : LimitDecomposition (lambdaT ≫ C.torusIso.hom ≫ C.torus.inclusion))
    (E : LimitDecomposition (oppositeCocharacter (lambdaT ≫ C.torusIso.hom ≫ C.torus.inclusion)))
    (hD : SameSubgroup D.centralizer C.torus)
    (hpos : IsSubgroupOf (subgroupOfSubgroup C.subgroup D.contracting) H)
    (hneg : IsSubgroupOf (subgroupOfSubgroup C.subgroup E.contracting) H) :
    IsSubgroupOf C.subgroup H := by
  let K := closedSubgroupAlgebraicGroup C.subgroup
  letI : Smooth K.val.X.hom := hC.1
  letI : GeometricallyConnected K.val.X.hom := hC.2.1
  letI : ConnectedSpace K.val.X.left :=
    GeometricallyConnected.connectedSpace_of_subsingleton K.val.X.hom
  letI : IrreducibleSpace C.subgroup.group.X.left := group_irreducible_of_connected K
  letI : Smooth C.subgroup.group.X.hom := hC.1
  letI : IsReduced C.subgroup.group.X.left :=
    isReduced_of_smooth_over_field C.subgroup.group.X.hom
  have htorus : IsSubgroupOf (subgroupOfSubgroup C.subgroup C.torus) H := by
    obtain ⟨j, hj⟩ := hTH
    refine ⟨C.torusIso.inv ≫ j, ?_⟩
    change (C.torusIso.inv ≫ j) ≫ H.inclusion = C.torus.inclusion ≫ C.subgroup.inclusion
    rw [Category.assoc, hj, ← C.torus_inclusion, Iso.inv_hom_id_assoc]
  have hzero : IsSubgroupOf (subgroupOfSubgroup C.subgroup D.centralizer) H := by
    obtain ⟨j, hj⟩ := hD.1
    apply subgroupOf_trans (B := subgroupOfSubgroup C.subgroup C.torus) _ htorus
    refine ⟨j, ?_⟩
    change j ≫ (C.torus.inclusion ≫ C.subgroup.inclusion) =
      D.centralizer.inclusion ≫ C.subgroup.inclusion
    exact (Category.assoc _ _ _).symm.trans
      (congrArg (· ≫ C.subgroup.inclusion) hj)
  obtain ⟨p, hp⟩ := hpos
  obtain ⟨n, hn⟩ := hneg
  obtain ⟨z, hz⟩ := hzero
  let m := bigCellMap D E
  letI : IsOpenImmersion m.left := CocharacterDynamics.bigCell K _ D E
  let X := E.contracting.group.X ⊗ (D.centralizer.group.X ⊗ D.contracting.group.X)
  let v : X ⟶ H.group.X :=
    (fst _ _ ≫ n.hom.hom) * (snd _ _ ≫ multiplyFactors z p)
  have hv : v ≫ H.inclusion.hom.hom = m ≫ C.subgroup.inclusion.hom.hom := by
    have hmap {A : GroupScheme k} {a : A ⟶ H.group} {b : A ⟶ C.subgroup.group}
        (h : a ≫ H.inclusion = b ≫ C.subgroup.inclusion) :
        a.hom.hom ≫ H.inclusion.hom.hom = b.hom.hom ≫ C.subgroup.inclusion.hom.hom :=
      congrArg (Grp.forget (SchemeOver k)).map h
    change p ≫ H.inclusion = D.contracting.inclusion ≫ C.subgroup.inclusion at hp
    change n ≫ H.inclusion = E.contracting.inclusion ≫ C.subgroup.inclusion at hn
    change z ≫ H.inclusion = D.centralizer.inclusion ≫ C.subgroup.inclusion at hz
    simp only [v, m, bigCellMap, multiplyFactors, MonObj.comp_mul, MonObj.mul_comp,
      Category.assoc, hmap hp, hmap hn, hmap hz]
    rfl
  have hclosed : IsClosed (C.subgroup.inclusion.hom.hom.left ⁻¹'
      Set.range H.inclusion.hom.hom.left) :=
    H.isClosedImmersion.isClosedEmbedding.isClosed_range.preimage
      C.subgroup.inclusion.hom.hom.left.continuous
  have hcontain : Set.range m.left ⊆ C.subgroup.inclusion.hom.hom.left ⁻¹'
      Set.range H.inclusion.hom.hom.left := by
    rintro _ ⟨x, rfl⟩
    refine ⟨v.left x, ?_⟩
    exact congrArg (fun f : X ⟶ G.val.X => f.left x) hv
  letI : Nonempty X.left := ⟨(lift η[E.contracting.group.X]
    (lift η[D.centralizer.group.X] η[D.contracting.group.X])).left (IsLocalRing.closedPoint k)⟩
  have hdense : Dense (Set.range m.left) :=
    m.left.isOpenEmbedding.isOpen_range.dense (Set.range_nonempty m.left)
  have hall : closure (Set.range m.left) ⊆
      C.subgroup.inclusion.hom.hom.left ⁻¹' Set.range H.inclusion.hom.hom.left :=
    closure_minimal hcontain hclosed
  have himage : Set.range C.subgroup.inclusion.hom.hom.left ⊆
      Set.range H.inclusion.hom.hom.left := by
    rintro _ ⟨x, rfl⟩
    apply hall
    rw [hdense.closure_eq]
    exact Set.mem_univ x
  obtain ⟨f, hf⟩ := factors_of_range_subset C.subgroup.inclusion.hom.hom
    H.inclusion.hom.hom H.isClosedImmersion himage
  exact factor_group_through_subgroup H C.subgroup.inclusion f hf

private theorem closureFieldSpecIsIso (k : Type u) [Field k] [IsAlgClosed k] :
    IsIso (fieldSpecMap k (AlgebraicClosure k)) := by
  haveI : IsIso (CommRingCat.ofHom (algebraMap k (AlgebraicClosure k))) :=
    (ConcreteCategory.isIso_iff_bijective _).mpr IsAlgClosed.algebraMap_bijective_of_isIntegral
  infer_instance

private abbrev schemeOverClosureEquivalence (k : Type u) [Field k] [IsAlgClosed k] :
    SchemeOver k ≌ SchemeOver (AlgebraicClosure k) := by
  letI := closureFieldSpecIsIso k
  let f := fieldSpecMap k (AlgebraicClosure k)
  refine CategoryTheory.Equivalence.mk (Over.pullback f) (Over.pullback (inv f)) ?_ ?_
  · exact (Over.pullbackId).symm ≪≫
      eqToIso (congrArg (fun g => Over.pullback g) (IsIso.inv_hom_id f).symm) ≪≫
      Over.pullbackComp (inv f) f
  · exact (Over.pullbackComp f (inv f)).symm ≪≫
      eqToIso (congrArg (fun g => Over.pullback g) (IsIso.hom_inv_id f)) ≪≫ Over.pullbackId

private def groupOverClosureEquivalence (k : Type u) [Field k] [IsAlgClosed k] :
    GroupScheme k ≌ GroupScheme (AlgebraicClosure k) := by
  let K := AlgebraicClosure k
  haveI : (baseChange k K).IsEquivalence := (schemeOverClosureEquivalence k).isEquivalence_functor
  haveI : (groupBaseChange k K).EssSurj :=
    ⟨fun G => (Functor.essImage_mapGrp (F := baseChange k K)).mpr
      (Functor.EssSurj.mem_essImage (F := baseChange k K) G.X)⟩
  haveI : (groupBaseChange k K).IsEquivalence := by constructor <;> infer_instance
  exact (groupBaseChange k K).asEquivalence

private theorem closureProjectionIsIso [IsAlgClosed k] (X : SchemeOver k) :
    IsIso (pullback.fst X.hom (fieldSpecMap k (AlgebraicClosure k))) := by
  letI := closureFieldSpecIsIso k
  infer_instance

private theorem closedImmersion_of_closure [IsAlgClosed k] {X Y : SchemeOver k} (f : X ⟶ Y)
    (hf : IsClosedImmersion ((baseChange k (AlgebraicClosure k)).map f).left) :
    IsClosedImmersion f.left := by
  let K := AlgebraicClosure k
  letI := closureProjectionIsIso X
  letI := closureProjectionIsIso Y
  letI := hf
  have h := (baseChangeMapIsPullback K f).w
  have hc : IsClosedImmersion (pullback.fst X.hom (fieldSpecMap k K) ≫ f.left) := by
    rw [← h]
    infer_instance
  exact (MorphismProperty.cancel_left_of_respectsIso (P := @IsClosedImmersion)
    (pullback.fst X.hom (fieldSpecMap k K)) f.left).mp hc

private theorem closureSubgroupDescends [IsAlgClosed k] {G : GroupScheme k}
    (S : ClosedSubgroup ((groupBaseChange k (AlgebraicClosure k)).obj G)) :
    ∃ (T : ClosedSubgroup G)
      (e : (groupBaseChange k (AlgebraicClosure k)).obj T.group ≅ S.group),
      (groupBaseChange k (AlgebraicClosure k)).map T.inclusion = e.hom ≫ S.inclusion := by
  let E := groupOverClosureEquivalence k
  let T := E.inverse.obj S.group
  let e := E.counitIso.app S.group
  let j := E.fullyFaithfulFunctor.preimage (e.hom ≫ S.inclusion)
  have hj : (groupBaseChange k (AlgebraicClosure k)).map j = e.hom ≫ S.inclusion :=
    E.fullyFaithfulFunctor.map_preimage _
  refine ⟨⟨T, j, ?_⟩, e, hj⟩
  apply closedImmersion_of_closure j.hom.hom
  change IsClosedImmersion ((groupBaseChange k (AlgebraicClosure k)).map j).hom.hom.left
  rw [hj]
  change IsClosedImmersion (e.hom.hom.hom.left ≫ S.inclusion.hom.hom.left)
  letI := S.isClosedImmersion
  letI : IsIso e.hom.hom.hom.left :=
    (Grp.forget (SchemeOver (AlgebraicClosure k)) ⋙ Over.forget _).map_isIso e.hom
  infer_instance

private theorem trivial_of_le_trivial {G : GroupScheme k} {S N : ClosedSubgroup G}
    (h : IsSubgroupOf S N) (hN : IsTrivialSubgroup N) : IsTrivialSubgroup S := by
  obtain ⟨f, hf⟩ := h
  obtain ⟨e⟩ := hN
  have hz := (Grp.isZero_trivial (SchemeOver k)).of_iso e
  have hf0 : f = 0 := hz.eq_of_tgt _ _
  letI := inclusion_mono S
  have hi0 : S.inclusion = 0 := by rw [← hf, hf0, zero_comp]
  exact ⟨(IsZero.of_mono_eq_zero S.inclusion hi0).iso (Grp.isZero_trivial _)⟩

private theorem trivial_over_closure_iff [IsAlgClosed k] (G : GroupScheme k) :
    Nonempty ((groupBaseChange k (AlgebraicClosure k)).obj G ≅
      Grp.trivial (SchemeOver (AlgebraicClosure k))) ↔
    Nonempty (G ≅ Grp.trivial (SchemeOver k)) := by
  let E := groupOverClosureEquivalence k
  constructor
  · rintro ⟨e⟩
    have h := (Grp.isZero_trivial _).of_iso e
    have hz : IsZero G := by
      refine ⟨fun X => ⟨⟨⟨0⟩, fun f => ?_⟩⟩, fun X => ⟨⟨⟨0⟩, fun f => ?_⟩⟩⟩
      · exact E.fullyFaithfulFunctor.map_injective (h.eq_of_src _ _)
      · exact E.fullyFaithfulFunctor.map_injective (h.eq_of_tgt _ _)
    exact ⟨hz.iso (Grp.isZero_trivial _)⟩
  · rintro ⟨e⟩
    have h := (Grp.isZero_trivial _).of_iso e
    have hz : IsZero (E.functor.obj G) := by
      refine ⟨fun X => ⟨⟨⟨0⟩, fun f => ?_⟩⟩, fun X => ⟨⟨⟨0⟩, fun f => ?_⟩⟩⟩
      · rw [← cancel_mono (E.counitIso.app X).inv]
        simpa only [E.fullyFaithfulFunctor.map_preimage] using
          congrArg E.functor.map
            (h.eq_of_src (E.fullyFaithfulFunctor.preimage _) (E.fullyFaithfulFunctor.preimage _))
      · rw [← cancel_epi (E.counitIso.app X).hom]
        simpa only [E.fullyFaithfulFunctor.map_preimage] using
          congrArg E.functor.map
            (h.eq_of_tgt (E.fullyFaithfulFunctor.preimage _) (E.fullyFaithfulFunctor.preimage _))
    exact ⟨hz.iso (Grp.isZero_trivial _)⟩

private theorem closureSubgroup_properties [IsAlgClosed k] (G : AffineAlgebraicGroup k)
    {S : ClosedSubgroup (GeometricGroup G).val} {T : ClosedSubgroup G.val}
    (e : (groupBaseChange k (AlgebraicClosure k)).obj T.group ≅ S.group)
    (he : (groupBaseChange k (AlgebraicClosure k)).map T.inclusion = e.hom ≫ S.inclusion)
    (hS : IsSmoothConnectedNormal S)
    (huS : IsUnipotent (closedSubgroupAlgebraicGroup S)) :
    IsSmoothConnectedNormal T ∧ IsUnipotent (closedSubgroupAlgebraicGroup T) := by
  let K := AlgebraicClosure k
  let X := (baseChange k K).obj T.group.X
  let p := pullback.fst T.group.X.hom (fieldSpecMap k K)
  let e' := ((Grp.forget (SchemeOver K)) ⋙ Over.forget _).mapIso e
  letI := closureProjectionIsIso T.group.X
  letI := closureFieldSpecIsIso k
  letI : IsIso e'.hom := inferInstance
  have hs : Smooth X.hom := by
    change Smooth ((groupBaseChange k K).obj T.group).X.hom
    rw [← Over.w e.hom.hom.hom]
    letI := hS.1
    change Smooth (e'.hom ≫ S.group.X.hom)
    infer_instance
  have hsT : Smooth T.group.X.hom := by
    apply (MorphismProperty.cancel_left_of_respectsIso (P := @Smooth) p T.group.X.hom).mp
    have hp : p ≫ T.group.X.hom = X.hom ≫ fieldSpecMap k K := pullback.condition
    rw [hp]
    letI := hs
    infer_instance
  letI := hS.2.1
  have hc : ConnectedSpace X.left := e'.hom.homeomorph.connectedSpace_iff.mpr hS.2.1
  letI := hc
  have hcT : ConnectedSpace T.group.X.left :=
    (asIso p).hom.homeomorph.connectedSpace_iff.mp hc
  have hn : IsNormalSubgroup ((groupBaseChange k K).map T.inclusion) :=
    normalSubgroup_of_iso (Iso.refl _) e ((Category.comp_id _).trans he) hS.2.2
  refine ⟨⟨hsT, hcT, (baseChangeNormalSubgroupIff k K T.inclusion T.isClosedImmersion).mp hn⟩, ?_⟩
  exact (Unipotent.unipotenceFieldExtension (K := K) (closedSubgroupAlgebraicGroup T)).mp
    (unipotent_iso e.symm huS)

private theorem normalUnipotentTrivial [IsAlgClosed k] (G : AffineAlgebraicGroup k)
    (hG : IsReductive G) (N : ClosedSubgroup G.val) (hN : IsSmoothConnectedNormal N)
    (hu : IsUnipotent (closedSubgroupAlgebraicGroup N)) : IsTrivialSubgroup N := by
  let K := AlgebraicClosure k
  have hcl := baseChangeClosedSubgroup k K N.inclusion N.isClosedImmersion
  let S := baseChangedSubgroup K N hcl
  have hs : Smooth S.group.X.hom :=
    MorphismProperty.pullback_snd _ _ hN.1
  letI := closureProjectionIsIso N.group.X
  letI := hN.2.1
  have hc : ConnectedSpace S.group.X.left :=
    (asIso (pullback.fst N.group.X.hom (fieldSpecMap k K))).hom.homeomorph.connectedSpace_iff.mpr
      hN.2.1
  have hn : IsNormalSubgroup S.inclusion := baseChangeNormalSubgroup k K N.inclusion hN.2.2
  have hu' : IsUnipotent (closedSubgroupAlgebraicGroup (G := GeometricGroup G) S) :=
    (Unipotent.unipotenceFieldExtension (K := K) (closedSubgroupAlgebraicGroup N)).mpr hu
  have hR := GeometricRadicals.geometricUnipotentRadicalLargest G
  have hSR : IsSubgroupOf S (geometricUnipotentRadical G) := hR.2.2 S ⟨hs, hc, hn⟩ hu'
  exact (trivial_over_closure_iff N.group).mp (trivial_of_le_trivial hSR hG.2.2)

private theorem reductive_of_normalUnipotentTrivial [IsAlgClosed k] (G : AffineAlgebraicGroup k)
    (hs : Smooth G.val.X.hom) (hc : GeometricallyConnected G.val.X.hom)
    (h : ∀ N : ClosedSubgroup G.val, IsSmoothConnectedNormal N →
      IsUnipotent (closedSubgroupAlgebraicGroup N) → IsTrivialSubgroup N) : IsReductive G := by
  let S := geometricUnipotentRadical G
  have hS := GeometricRadicals.geometricUnipotentRadicalLargest G
  obtain ⟨N, e, he⟩ := closureSubgroupDescends S
  obtain ⟨hN, huN⟩ := closureSubgroup_properties G e he hS.1 hS.2.1
  obtain ⟨t⟩ := (trivial_over_closure_iff N.group).mpr (h N hN huN)
  exact ⟨hs, hc, ⟨e.symm ≪≫ t⟩⟩

private theorem geometricGroupReductive (G : AffineAlgebraicGroup k)
    (hG : IsReductive G) : IsReductive (GeometricGroup G) := by
  apply reductive_of_normalUnipotentTrivial
  · exact MorphismProperty.pullback_snd _ _ hG.1
  · exact MorphismProperty.pullback_snd _ _ hG.2.1
  intro N hN hu
  exact trivial_of_le_trivial
    ((GeometricRadicals.geometricUnipotentRadicalLargest G).2.2 N hN hu) hG.2.2

private theorem reductive_of_geometricGroupReductive (G : AffineAlgebraicGroup k)
    (hs : Smooth G.val.X.hom) (hc : GeometricallyConnected G.val.X.hom)
    (hG : IsReductive (GeometricGroup G)) : IsReductive G := by
  have hR := GeometricRadicals.geometricUnipotentRadicalLargest G
  exact ⟨hs, hc, normalUnipotentTrivial (GeometricGroup G) hG _ hR.1 hR.2.1⟩

private theorem maximalTorus_over_closure [IsAlgClosed k] (G : AffineAlgebraicGroup k)
    (T : ClosedSubgroup G.val) (hT : IsMaximalTorus T) :
    Specs.RankOneFlag.IsGeometricallyMaximal T := by
  let K := AlgebraicClosure k
  let F := groupBaseChange k K
  let E := groupOverClosureEquivalence k
  have hcl := baseChangeClosedSubgroup k K T.inclusion T.isClosedImmersion
  refine ⟨hcl, ⟨torus_baseChange_algClosure (closedSubgroupAlgebraicGroup T) hT.1, ?_⟩⟩
  intro S hS hTS
  obtain ⟨U, e, he⟩ := closureSubgroupDescends S
  have hU : IsTorus U.group := by
    have hs : IsSplitTorus S.group :=
      split_of_torus ((isTorus_iff_coordinates
        (closedSubgroupAlgebraicGroup (G := GeometricGroup G) S)).mp hS)
    obtain ⟨n, ⟨a⟩⟩ := hs
    exact ⟨K, inferInstance, inferInstance, inferInstance, n, ⟨e ≪≫ a⟩⟩
  obtain ⟨v, hv⟩ := hTS
  let j := E.fullyFaithfulFunctor.preimage (v ≫ e.inv)
  have hj : F.map j = v ≫ e.inv := E.fullyFaithfulFunctor.map_preimage _
  have hjT : j ≫ U.inclusion = T.inclusion := by
    apply E.fullyFaithfulFunctor.map_injective
    change F.map (j ≫ U.inclusion) = F.map T.inclusion
    rw [Functor.map_comp, hj, he, Category.assoc, Iso.inv_hom_id_assoc]
    exact hv
  obtain ⟨w, hw⟩ := hT.2 U hU ⟨j, hjT⟩
  refine ⟨e.inv ≫ F.map w, ?_⟩
  change (e.inv ≫ F.map w) ≫ F.map T.inclusion = S.inclusion
  rw [Category.assoc, ← Functor.map_comp, hw, he, Iso.inv_hom_id_assoc]

/-- A factorization of conjugation through a closed subgroup gives its action
by group automorphisms. -/
private def actionOfConjugation {G T A : GroupScheme k} (t : T ⟶ G) (j : A ⟶ G)
    (hj : IsClosedImmersion j.hom.hom.left) (a : T.X ⊗ A.X ⟶ A.X)
    (ha : a ≫ j.hom.hom = (fst T.X A.X ≫ t.hom.hom) * (snd T.X A.X ≫ j.hom.hom) *
      (fst T.X A.X ≫ t.hom.hom)⁻¹) : AutomorphismAction T A := by
  letI : Mono j.hom.hom := mono_over _ hj
  have h {X : SchemeOver k} (u : X ⟶ T.X) (x : X ⟶ A.X) :
      (lift u x ≫ a) ≫ j.hom.hom = (u ≫ t.hom.hom) * (x ≫ j.hom.hom) *
        (u ≫ t.hom.hom)⁻¹ := by
    rw [Category.assoc, ha]
    simp only [MonObj.comp_mul, GrpObj.comp_inv, lift_fst_assoc, lift_snd_assoc]
  refine ⟨a, ?_, ?_, ?_, ?_⟩
  · intro R x
    apply (cancel_mono j.hom.hom).mp
    rw [h, MonObj.one_comp]
    simp
  · intro R u v x
    apply (cancel_mono j.hom.hom).mp
    rw [h, h, h, MonObj.mul_comp]
    group
  · intro R u
    apply (cancel_mono j.hom.hom).mp
    rw [h, MonObj.one_comp, mul_one, mul_inv_cancel]
  · intro R u x y
    apply (cancel_mono j.hom.hom).mp
    rw [h, MonObj.mul_comp, MonObj.mul_comp, h, h]
    group

private theorem restrictConjugationToNormal {B T : GroupScheme k} (t : T ⟶ B)
    (N : ClosedSubgroup B) (hN : IsNormalSubgroup N.inclusion) :
    ∃ a : AutomorphismAction T N.group, ∀ (R : TestAlgebra k) (s : GroupPoints T R)
      (x : GroupPoints N.group R),
      onPoints N.inclusion R (pointAction a R s x) =
        onPoints t R s * onPoints N.inclusion R x * (onPoints t R s)⁻¹ := by
  obtain ⟨a, ha⟩ := normalSubgroup_conjugate_sections hN
    (fst T.X N.group.X ≫ t.hom.hom) (snd T.X N.group.X)
  refine ⟨actionOfConjugation t N.inclusion N.isClosedImmersion a ?_, ?_⟩
  · simpa only [Category.assoc] using ha
  · intro R s x
    change (lift s x ≫ a) ≫ N.inclusion.hom.hom = _
    rw [Category.assoc, ha]
    simp only [MonObj.comp_mul, GrpObj.comp_inv, lift_fst_assoc, lift_snd_assoc]
    rfl

private theorem restrictConjugationToStable {B T U : AffineAlgebraicGroup k}
    (t : T.val ⟶ B.val) (N : ClosedSubgroup B.val) (a : AutomorphismAction T.val N.group)
    (ha : ∀ (R : TestAlgebra k) (s : GroupPoints T.val R) (x : GroupPoints N.group R),
      onPoints N.inclusion R (pointAction a R s x) =
        onPoints t R s * onPoints N.inclusion R x * (onPoints t R s)⁻¹)
    (d : U.val ⟶ N.group) (hd : IsClosedImmersion d.hom.hom.left) (hst : IsStable a d) :
    ∃ b : AutomorphismAction T.val U.val, ∀ (R : TestAlgebra k) (s : GroupPoints T.val R)
      (x : GroupPoints U.val R),
      onPoints (d ≫ N.inclusion) R (pointAction b R s x) =
        onPoints t R s * onPoints (d ≫ N.inclusion) R x * (onPoints t R s)⁻¹ := by
  let X := T.val.X ⊗ U.val.X
  letI := T.property.1
  letI := U.property.1
  have hX : IsAffine X.left := by
    change IsAffine (pullback T.val.X.hom U.val.X.hom)
    infer_instance
  obtain ⟨A, ⟨e⟩⟩ := (essImage_algSpec (R := CommRingCat.of k)).mpr hX
  let R : TestAlgebra k := A.unop
  let s : GroupPoints T.val R := e.hom ≫ fst T.val.X U.val.X
  let x : GroupPoints U.val R := e.hom ≫ snd T.val.X U.val.X
  obtain ⟨y, hy⟩ := hst R s x
  let b := e.inv ≫ y
  let i := d ≫ N.inclusion
  have hE : e.hom ≫ (b ≫ i.hom.hom) =
      e.hom ≫ ((fst T.val.X U.val.X ≫ t.hom.hom) *
        (snd T.val.X U.val.X ≫ i.hom.hom) * (fst T.val.X U.val.X ≫ t.hom.hom)⁻¹) := by
    change (e.hom ≫ e.inv ≫ y ≫ d.hom.hom ≫ N.inclusion.hom.hom) = _
    rw [Iso.hom_inv_id_assoc]
    change (onPoints d R y) ≫ N.inclusion.hom.hom = _
    rw [hy]
    exact (ha R s (onPoints d R x)).trans (by
      simp only [s, x, i, MonObj.comp_mul, GrpObj.comp_inv]
      rfl)
  have hb := (cancel_epi e.hom).mp hE
  letI := N.isClosedImmersion
  have hi : IsClosedImmersion i.hom.hom.left := IsClosedImmersion.comp _ _
  refine ⟨actionOfConjugation t i hi b hb, ?_⟩
  intro R' s' x'
  change (lift s' x' ≫ b) ≫ i.hom.hom = _
  rw [Category.assoc, hb]
  simp only [MonObj.comp_mul, GrpObj.comp_inv, lift_fst_assoc, lift_snd_assoc]
  rfl

private theorem exists_additive_normalized_subgroup [IsAlgClosed k]
    (B T : AffineAlgebraicGroup k) (t : T.val ⟶ B.val) (ht : IsSplitTorus T.val)
    (N : ClosedSubgroup B.val) (hN : IsSmoothConnectedNormal N)
    (hu : IsUnipotent (closedSubgroupAlgebraicGroup N)) (hnt : ¬ IsTrivialSubgroup N) :
    ∃ (D : AffineAlgebraicGroup k)
      (d : D.val ⟶ N.group) (_ : IsClosedImmersion d.hom.hom.left)
      (b : AutomorphismAction T.val D.val)
      (_ : (groupPointsFunctor k).obj D.val ≅ StandardGroups.additivePoints k),
      Smooth D.val.X.hom ∧ ConnectedSpace D.val.X.left ∧
      ∀ (R : TestAlgebra k) (s : GroupPoints T.val R) (x : GroupPoints D.val R),
        onPoints (d ≫ N.inclusion) R (pointAction b R s x) =
          onPoints t R s * onPoints (d ≫ N.inclusion) R x * (onPoints t R s)⁻¹ := by
  obtain ⟨a, ha⟩ := restrictConjugationToNormal t N hN.2.2
  obtain ⟨n, S, hS, hst⟩ := EquivariantUnipotentSeries.stableSeriesForTorusAction
    (closedSubgroupAlgebraicGroup N) T hN.1 hN.2.1 hu ht a
  cases n with
  | zero => exact False.elim (hnt ⟨S.top.symm ≪≫ S.bottom⟩)
  | succ n =>
    obtain ⟨Q, q, hq, ⟨e⟩⟩ := hS.2.2 n (Nat.lt_succ_self n)
    let D := S.term n
    let d := S.inclusion n
    have hd := closedSeries_inclusion_closed S n
    haveI : IsIso q := isIso_of_trivial_kernel q ⟨_, S.step n, S.closed n⟩ hq ⟨S.bottom⟩
    obtain ⟨b, hb⟩ := restrictConjugationToStable (U := D) t N a ha d hd
      (hst n (Nat.le_succ n))
    obtain ⟨hsD, hcD⟩ := hS.2.1 n (Nat.le_succ n)
    exact ⟨D, d, hd, b, (groupPointsFunctor k).mapIso (asIso q) ≪≫ e, hsD, hcD, hb⟩

private def additivePoint {D : GroupScheme k}
    (e : (groupPointsFunctor k).obj D ≅ StandardGroups.additivePoints k)
    (R : TestAlgebra k) (b : R) : GroupPoints D R :=
  e.inv.app R (Multiplicative.ofAdd b)

private theorem additivePoint_natural {D : GroupScheme k}
    (e : (groupPointsFunctor k).obj D ≅ StandardGroups.additivePoints k)
    {R S : TestAlgebra k} (a : R ⟶ S) (b : R) :
    mapPoints a (additivePoint e R b) = additivePoint e S (a.hom b) := by
  exact (NatTrans.naturality_apply e.inv a (Multiplicative.ofAdd b)).symm

private theorem characterValue_composition {A B : GroupScheme k}
    (α : Character B) (f : A ⟶ B) (R : TestAlgebra k) (t : GroupPoints A R) :
    characterValue (f ≫ α) R t = characterValue α R (onPoints f R t) := by
  have h : t ≫ (f ≫ α).hom.hom = onPoints f R t ≫ α.hom.hom := by
    change t ≫ (f.hom.hom ≫ α.hom.hom) = (t ≫ f.hom.hom) ≫ α.hom.hom
    exact (Category.assoc _ _ _).symm
  unfold characterValue
  dsimp only
  rw [h]

private theorem characterValue_natural {T : GroupScheme k} (α : Character T)
    {R S : TestAlgebra k} (a : R ⟶ S) (t : GroupPoints T R) :
    characterValue α S (mapPoints a t) = a.hom (characterValue α R t) := by
  let F := algSpec (CommRingCat.of k)
  let ff := algSpec.fullyFaithful (R := CommRingCat.of k)
  let p := t ≫ α.hom.hom
  let f := ff.preimage p
  have hf : F.map f = p := ff.map_preimage _
  unfold characterValue
  change (ff.preimage ((F.map a.op ≫ t) ≫ α.hom.hom)).unop.hom
      (MonoidAlgebra.single integerGenerator 1) =
    a.hom (f.unop.hom (MonoidAlgebra.single integerGenerator 1))
  rw [Category.assoc, ← show p = t ≫ α.hom.hom from rfl, ← hf, ← Functor.map_comp,
    ff.preimage_map]
  rfl

private theorem characterValue_standard {T : GroupScheme k} (α : Character T)
    (R : TestAlgebra k) (t : GroupPoints T R) :
    characterValue α R t =
      (show Rˣ from (StandardGroups.multiplicativeGroupPointsIso k).hom.app R
        (onPoints (α ≫ (DiagonalizableGroups.multiplicativeGroupIso k).hom) R t)).val := by
  let A := groupAlgebra k IntegerCharacters
  let F := groupPointsFunctor k
  let q := (F.map α).app R t
  obtain ⟨b, hb⟩ := (ConcreteCategory.bijective_of_isIso ((hopfSpecPointIso A).hom.app R)).2 q
  have h := ConcreteCategory.congr_hom (congrArg (fun a => a.app R)
    (toMultiplicativeGroup_points (StandardGroups.multiplicativeGroup k)
      (StandardGroups.multiplicativeGroupPointsIso k))) q
  change (StandardGroups.multiplicativeGroupPointsIso k).hom.app R
      ((F.map (DiagonalizableGroups.multiplicativeGroupIso k).hom).app R q) =
    (show Rˣ from ((DiagonalizableGroups.groupAlgebraPointsIso k IntegerCharacters ≪≫
      integerPointsIso).hom.app R q)) at h
  have hp : characterValue α R t = b.ofConv (MonoidAlgebra.single integerGenerator 1) := by
    unfold characterValue
    change ((algSpec.fullyFaithful (R := CommRingCat.of k)).preimage q).unop.hom
      (MonoidAlgebra.single integerGenerator 1) = _
    rw [← hb]
    change ((algSpec.fullyFaithful (R := CommRingCat.of k)).preimage
      ((testSpec k).map (CommAlgCat.ofHom b.ofConv).op)).unop.hom _ = _
    rw [Functor.FullyFaithful.preimage_map]
    rfl
  change characterValue α R t =
    (show Rˣ from (StandardGroups.multiplicativeGroupPointsIso k).hom.app R
      ((F.map (α ≫ (DiagonalizableGroups.multiplicativeGroupIso k).hom)).app R t)).val
  rw [Functor.map_comp]
  change characterValue α R t = (show Rˣ from
    (StandardGroups.multiplicativeGroupPointsIso k).hom.app R
      ((F.map (DiagonalizableGroups.multiplicativeGroupIso k).hom).app R q)).val
  rw [h, hp, ← hb]
  exact (pointsIso_spec IntegerCharacters R b.ofConv integerGenerator).symm

private theorem scalarCharacterOfAdditiveConjugation {B T D : AffineAlgebraicGroup k}
    (t : T.val ⟶ B.val) (i : D.val ⟶ B.val)
    (a : AutomorphismAction T.val D.val)
    (e : (groupPointsFunctor k).obj D.val ≅ StandardGroups.additivePoints k)
    (ht : Smooth T.val.X.hom)
    (ha : ∀ (R : TestAlgebra k) (s : GroupPoints T.val R) (x : GroupPoints D.val R),
      onPoints i R (pointAction a R s x) =
        onPoints t R s * onPoints i R x * (onPoints t R s)⁻¹) :
    ∃ χ : Character T.val, ∀ (R : TestAlgebra k) (s : GroupPoints T.val R) (x : R),
      onPoints t R s * onPoints i R (additivePoint e R x) * (onPoints t R s)⁻¹ =
        onPoints i R (additivePoint e R (characterValue χ R s * x)) := by
  obtain ⟨χ, hχ⟩ := action_character a e ht
  let d := DiagonalizableGroups.multiplicativeGroupIso k
  refine ⟨χ ≫ d.inv, ?_⟩
  intro R s x
  rw [← ha]
  apply congrArg (onPoints i R)
  apply (ConcreteCategory.bijective_of_isIso (e.hom.app R)).1
  have hval := hχ R s x
  change Multiplicative.toAdd
      (show Multiplicative R from e.hom.app R (pointAction a R s (additivePoint e R x))) =
    (show Rˣ from (StandardGroups.multiplicativeGroupPointsIso k).hom.app R
      (onPoints χ R s)).val * x at hval
  have heval := characterValue_standard (χ ≫ d.inv) R s
  rw [Category.assoc, d.inv_hom_id, Category.comp_id] at heval
  have hcomp := ConcreteCategory.congr_hom (e.inv_hom_id_app R)
    (Multiplicative.ofAdd (characterValue (χ ≫ d.inv) R s * x))
  exact (Multiplicative.toAdd.injective (hval.trans (congrArg (· * x) heval).symm)).trans
    hcomp.symm

private def additiveTangent {D : GroupScheme k}
    (e : (groupPointsFunctor k).obj D ≅ StandardGroups.additivePoints k) : Lie k D := by
  refine ⟨additivePoint e (CommAlgCat.of k (DualNumber k)) DualNumber.eps, ?_⟩
  change mapPoints (dualReduction k) (additivePoint e _ DualNumber.eps) = 1
  rw [additivePoint_natural]
  change (e.inv.app _).hom 1 = 1
  exact map_one (e.inv.app _).hom

private theorem additiveTangent_ne_zero {D : GroupScheme k}
    (e : (groupPointsFunctor k).obj D ≅ StandardGroups.additivePoints k) :
    additiveTangent e ≠ 0 := by
  intro h
  have hv := congrArg (fun p : Lie k D => p.toMul.val) h
  change (e.inv.app (CommAlgCat.of k (DualNumber k))).hom
    (Multiplicative.ofAdd DualNumber.eps) = 1 at hv
  rw [← map_one (e.inv.app (CommAlgCat.of k (DualNumber k))).hom] at hv
  have hh := (ConcreteCategory.bijective_of_isIso
    (e.inv.app (CommAlgCat.of k (DualNumber k)))).1 hv
  have he : (DualNumber.eps : DualNumber k) = 0 := congrArg Multiplicative.toAdd hh
  exact one_ne_zero (congrArg TrivSqZeroExt.snd he)

private theorem onPoints_mapPoints {D B : GroupScheme k} (i : D ⟶ B)
    {R S : TestAlgebra k} (a : R ⟶ S) (x : GroupPoints D R) :
    mapPoints a (onPoints i R x) = onPoints i S (mapPoints a x) := by
  change (testSpec k).map a.op ≫ (x ≫ i.hom.hom) =
    ((testSpec k).map a.op ≫ x) ≫ i.hom.hom
  exact (Category.assoc _ _ _).symm

private theorem additiveTangent_hasWeight {G D : GroupScheme k} (T : ClosedSubgroup G)
    (i : D ⟶ G) (e : (groupPointsFunctor k).obj D ≅ StandardGroups.additivePoints k)
    (χ : Character T.group)
    (h : ∀ (R : TestAlgebra k) (t : GroupPoints T.group R) (x : R),
      onPoints T.inclusion R t * onPoints i R (additivePoint e R x) *
        (onPoints T.inclusion R t)⁻¹ =
        onPoints i R (additivePoint e R (characterValue χ R t * x))) :
    mapPointKernel i (additiveTangent e) ∈ adjointWeightVectors T χ := by
  intro R t
  let A := CommAlgCat.of k (DualNumber R)
  let a := dualMap (CommAlgCat.ofHom (Algebra.ofId k R))
  change (mapPoints (constants R) (onPoints T.inclusion R t) : GroupPoints G A) *
      mapPoints a (onPoints i _ (additivePoint e _ DualNumber.eps)) *
        (mapPoints (constants R) (onPoints T.inclusion R t))⁻¹ =
    mapPoints (scale R (characterValue χ R t))
      (mapPoints a (onPoints i _ (additivePoint e _ DualNumber.eps)))
  rw [onPoints_mapPoints, onPoints_mapPoints, additivePoint_natural]
  have he : a.hom DualNumber.eps = (DualNumber.eps : DualNumber R) :=
    TrivSqZeroExt.ext (map_zero (Algebra.ofId k R)) (map_one (Algebra.ofId k R))
  rw [he, h A (mapPoints (constants R) t) DualNumber.eps,
    onPoints_mapPoints, additivePoint_natural, characterValue_natural]
  congr 2
  apply TrivSqZeroExt.ext
  · change characterValue χ R t * 0 = 0
    exact mul_zero _
  · change characterValue χ R t * 1 + 0 * 0 = characterValue χ R t * 1
    rw [zero_mul, add_zero]

private theorem centralizes_of_trivial_restricted_character {G D S : GroupScheme k}
    (T : ClosedSubgroup G) (s : S ⟶ T.group) (i : D ⟶ G)
    (e : (groupPointsFunctor k).obj D ≅ StandardGroups.additivePoints k)
    (χ : Character T.group) (hχ : s ≫ χ = 1)
    (h : ∀ (R : TestAlgebra k) (t : GroupPoints T.group R) (x : R),
      onPoints T.inclusion R t * onPoints i R (additivePoint e R x) *
        (onPoints T.inclusion R t)⁻¹ =
        onPoints i R (additivePoint e R (characterValue χ R t * x))) :
    Centralizes (s ≫ T.inclusion) i.hom.hom := by
  apply (centralizes_iff_affine _ _).mpr
  intro R x g
  obtain ⟨b, rfl⟩ := (ConcreteCategory.bijective_of_isIso (e.inv.app R)).2 x
  have hval : characterValue χ R (onPoints s R g) = 1 := by
    rw [← characterValue_composition, hχ, characterValue_one]
  have hc := h R (onPoints s R g) (Multiplicative.toAdd b)
  rw [hval, one_mul, ← onPoints_comp] at hc
  exact (mul_inv_eq_iff_eq_mul.mp hc).symm

private theorem normalIntersection_additive_trivial [IsAlgClosed k]
    (B C D : AffineAlgebraicGroup k) (j : C.val ⟶ B.val)
    (hj : IsClosedImmersion j.hom.hom.left) (hC : IsReductive C)
    (N : ClosedSubgroup B.val) (hN : IsNormalSubgroup N.inclusion)
    (hu : IsUnipotent (closedSubgroupAlgebraicGroup N))
    (d : D.val ⟶ N.group) (hd : IsClosedImmersion d.hom.hom.left)
    (c : D.val ⟶ C.val) (heq : c ≫ j = d ≫ N.inclusion)
    (hs : Smooth D.val.X.hom) (hc : ConnectedSpace D.val.X.left) :
    Nonempty (D.val ≅ Grp.trivial (SchemeOver k)) := by
  let P := pullback j N.inclusion
  let p := pullback.fst j N.inclusion
  let q := pullback.snd j N.inclusion
  have hp : IsPullback p.hom.hom q.hom.hom j.hom.hom N.inclusion.hom.hom :=
    (Grp.forget (SchemeOver k)).map_isPullback (.of_hasPullback j N.inclusion)
  have hp' := hp.map (Over.forget _)
  have hpcl : IsClosedImmersion p.hom.hom.left :=
    MorphismProperty.of_isPullback hp'.flip N.isClosedImmersion
  have hqcl : IsClosedImmersion q.hom.hom.left :=
    MorphismProperty.of_isPullback hp' hj
  let I : ClosedSubgroup C.val := ⟨P, p, hpcl⟩
  let J : ClosedSubgroup N.group := ⟨P, q, hqcl⟩
  have hI : IsNormalSubgroup I.inclusion := by
    let X := C.val.X ⊗ P.X
    let g : X ⟶ C.val.X := fst _ _
    let x : X ⟶ P.X := snd _ _
    obtain ⟨n, hn⟩ := normalSubgroup_conjugate_sections hN
      (g ≫ j.hom.hom) (x ≫ q.hom.hom)
    let y : X ⟶ C.val.X := g * (x ≫ p.hom.hom) * g⁻¹
    have hy : y ≫ j.hom.hom = n ≫ N.inclusion.hom.hom := by
      have hw : p.hom.hom ≫ j.hom.hom = q.hom.hom ≫ N.inclusion.hom.hom := hp.w
      rw [hn]
      simp only [y, MonObj.mul_comp, GrpObj.inv_comp, Category.assoc, hw]
    exact ⟨hp.lift y n hy, hp.lift_fst y n hy⟩
  let A := closedSubgroupAlgebraicGroup I
  obtain ⟨K⟩ := EquivariantUnipotentSeries.exists_smooth_identity_component A
  let L := subgroupOfSubgroup I K.subgroup
  letI := hC.2.1
  letI : ConnectedSpace C.val.X.left :=
    GeometricallyConnected.connectedSpace_of_subsingleton C.val.X.hom
  have hnL : IsNormalSubgroup L.inclusion :=
    EquivariantUnipotentSeries.smooth_identity_component_normal hC.1 inferInstance I hI K
  have huP := Unipotent.closedSubgroupsUnipotent (closedSubgroupAlgebraicGroup N) J hu
  have huL : IsUnipotent (closedSubgroupAlgebraicGroup L) :=
    Unipotent.closedSubgroupsUnipotent A K.subgroup huP
  have htL := normalUnipotentTrivial C hC L ⟨K.smooth, K.connected, hnL⟩ huL
  let l : D.val ⟶ P := pullback.lift c d heq
  obtain ⟨m, hm⟩ := ReducedIdentityComponent.factorHom K (A := D) l hs hc
  obtain ⟨e⟩ := htL
  have hm0 : m = 0 := ((Grp.isZero_trivial _).of_iso e).eq_of_tgt _ _
  have hd0 : d = 0 := by
    rw [← show l ≫ q = d from pullback.lift_snd _ _ _, ← hm, hm0]
    simp
  let D' : ClosedSubgroup N.group := ⟨D.val, d, hd⟩
  letI : Mono d := inclusion_mono D'
  exact ⟨(IsZero.of_mono_eq_zero d hd0).iso (Grp.isZero_trivial _)⟩

private theorem additive_points_not_trivial {D : GroupScheme k}
    (e : (groupPointsFunctor k).obj D ≅ StandardGroups.additivePoints k) :
    ¬ Nonempty (D ≅ Grp.trivial (SchemeOver k)) := by
  rintro ⟨a⟩
  have he := (cancel_mono a.hom.hom.hom).mp
    (isTerminalTensorUnit.hom_ext
      (additivePoint e (CommAlgCat.of k k) 0 ≫ a.hom.hom.hom)
      (additivePoint e (CommAlgCat.of k k) 1 ≫ a.hom.hom.hom))
  have hz := (ConcreteCategory.bijective_of_isIso (e.inv.app (CommAlgCat.of k k))).1 he
  exact zero_ne_one (congrArg Multiplicative.toAdd hz)

set_option maxHeartbeats 2500000 in
/-- The symmetric-root criterion, with the six frozen root-data premises. -/
theorem reductiveOfSymmetricRoots_conditional
    (_centralizer : Specs.RankOneFlag.CentralizerAndPositiveCocharacter.{u})
    (_projective : Specs.RankOneFlag.ProjectiveLineAutomorphisms.{u})
    (_flag : Specs.RankOneFlag.RankOneFlagGeometry.{u})
    (rankOne : Specs.RootGroups.RankOneRootGroups.{u})
    (_dimension : Specs.RootGroups.RootDimension.{u})
    (_rootGroups : Specs.RootGroups.RootSubgroups.{u}) :
    ReductiveOfSymmetricRoots.{u} := by
  intro k _ _ G hG H hsH hcH T hT hTH hsymm hroot
  let B := closedSubgroupAlgebraicGroup H
  let A := closedSubgroupAlgebraicGroup T
  have hmax := maximalTorus_over_closure G T hT
  have hsplit : IsSplitTorus T.group := split_of_torus ((isTorus_iff_coordinates A).mp hT.1)
  have hsm : Smooth T.group.X.hom := (torus_smooth_connected_solvable A hT.1).1
  apply reductive_of_normalUnipotentTrivial B hsH hcH
  intro N hN hu
  by_contra hn
  obtain ⟨t, ht⟩ := hTH
  obtain ⟨V, d, hd, a, e, hsV, hcV, ha⟩ :=
    exists_additive_normalized_subgroup B A t hsplit N hN hu hn
  let b : V.val ⟶ B.val := d ≫ N.inclusion
  let i : V.val ⟶ G.val := b ≫ H.inclusion
  letI := H.isClosedImmersion
  letI := N.isClosedImmersion
  letI := hd
  have hi : IsClosedImmersion i.hom.hom.left := by
    change IsClosedImmersion ((d.hom.hom.left ≫ N.inclusion.hom.hom.left) ≫
      H.inclusion.hom.hom.left)
    infer_instance
  obtain ⟨χ, hχ⟩ := scalarCharacterOfAdditiveConjugation (B := B) (T := A) (D := V) t b a e hsm ha
  have hscalar (R : TestAlgebra k) (s : GroupPoints T.group R) (x : R) :
      onPoints T.inclusion R s * onPoints i R (additivePoint e R x) *
        (onPoints T.inclusion R s)⁻¹ =
        onPoints i R (additivePoint e R (characterValue χ R s * x)) := by
    let F := onPoints H.inclusion R
    have htR : onPoints T.inclusion R s = F (onPoints t R s) := by
      calc
        _ = onPoints (t ≫ H.inclusion) R s := congrArg (fun a => onPoints a R s) ht.symm
        _ = _ := onPoints_comp t H.inclusion R s
    have hiR (y : GroupPoints V.val R) : onPoints i R y = F (onPoints b R y) :=
      onPoints_comp b H.inclusion R y
    have he := congrArg F (hχ R s x)
    rw [map_mul, map_mul, map_inv] at he
    simp only [htR, hiR]
    exact he
  have hχn : χ ≠ 1 := by
    intro hχ₀
    have hcen := centralizes_of_trivial_restricted_character T (𝟙 T.group) i e χ
      (by rw [Category.id_comp, hχ₀]) hscalar
    rw [Category.id_comp] at hcen
    have hcent := Reductive.TorusCentralizer.maximalTorusCentralizer G hG T hT.1 hmax
    obtain ⟨f, hf⟩ := (hcent V.val.X i.hom.hom).mp hcen
    obtain ⟨j, hj⟩ := factor_group_through_subgroup T i f hf
    have huV := Unipotent.closedSubgroupsUnipotent (closedSubgroupAlgebraicGroup N)
      ⟨V.val, d, hd⟩ hu
    have hmT := torus_multiplicativeType ((isTorus_iff_coordinates A).mp hT.1)
    have hj0 : j = 0 := Unipotent.homFromUnipotentToMultiplicativeType V A j huV hmT
    have hi0 : i = 0 := by rw [← hj, hj0, zero_comp]
    let I : ClosedSubgroup G.val := ⟨V.val, i, hi⟩
    letI : Mono i := inclusion_mono I
    exact additive_points_not_trivial e
      ⟨(IsZero.of_mono_eq_zero i hi0).iso (Grp.isZero_trivial _)⟩
  let v := mapPointKernel i (additiveTangent e)
  have hv := additiveTangent_hasWeight T i e χ hscalar
  have hv0 : v ≠ 0 := by
    intro hz
    apply additiveTangent_ne_zero e
    have hp := congrArg (fun w : Lie k G.val => w.toMul.val)
      (hz.trans (map_zero (mapPointKernel i)).symm)
    have hq := onPoints_injective i hi (CommAlgCat.of k (DualNumber k)) hp
    exact Subtype.ext hq
  have hvH : v ∈ CocharacterDynamics.lieImage H := by
    refine ⟨mapPointKernel b (additiveTangent e), ?_⟩
    exact ((lieFunctoriality k).2.2 V.val B.val G.val b H.inclusion _).symm
  have hχH : χ ∈ subgroupRoots T H := ⟨hχn, v, hv, hvH, hv0⟩
  have hχG : χ ∈ absoluteRoots T := ⟨hχn, v, hv, hv0⟩
  obtain ⟨C, _, hC, _, Dpos, Dneg, hpair, _, _, _, _, _, _, hpos, hneg, _⟩ :=
    rankOne G hG T hsplit hmax χ hχG
  obtain ⟨j, hj⟩ := containsRankOneCentralizer G H T ⟨t, ht⟩ C hC Dpos Dneg hpair.1
    (hroot χ hχH _ hpos) (hroot χ⁻¹ (hsymm χ hχH) _ hneg)
  have hcen := centralizes_of_trivial_restricted_character T C.kernelTorus.inclusion i e χ
    C.kernelTorus_largest.2.1 hscalar
  obtain ⟨c, hc⟩ := (C.centralizes V.val.X i.hom.hom).mp hcen
  obtain ⟨c', hc'⟩ := factor_group_through_subgroup C.subgroup i c hc
  have hcB : c' ≫ j = d ≫ N.inclusion := by
    letI := inclusion_mono H
    apply (cancel_mono H.inclusion).mp
    rw [Category.assoc, hj, hc']
  exact additive_points_not_trivial e
    (normalIntersection_additive_trivial B (closedSubgroupAlgebraicGroup C.subgroup) V
      j (factor_closed hj) hC N hN.2.2 hu d hd c' hcB hsV hcV)

private theorem dualReduction_surjective_on_spectrum :
    Function.Surjective ((testSpec k).map (dualReduction k).op).left := by
  let f := (TrivSqZeroExt.fstHom k k k).toRingHom
  change Function.Surjective (PrimeSpectrum.comap f)
  rw [← Set.range_eq_univ, range_comap_of_surjective _ _]
  · apply Set.eq_univ_of_forall
    intro x
    apply (PrimeSpectrum.mem_zeroLocus x _).mpr
    intro z hz
    have hz₁ : z.fst = 0 := RingHom.mem_ker.mp hz
    have hz₂ : z ^ 2 = 0 := by
      rw [pow_two]
      apply TrivSqZeroExt.ext
      · change z.fst * z.fst = 0
        simp [hz₁]
      · change z.fst * z.snd + z.snd * z.fst = 0
        simp [hz₁]
    exact x.isPrime.mem_of_pow_mem (n := 2) (hz₂ ▸ x.asIdeal.zero_mem)
  · intro x
    exact ⟨TrivSqZeroExt.inl x, rfl⟩

private theorem tangent_surjective_of_open {G : GroupScheme k} (H : ClosedSubgroup G)
    (hH : IsOpenImmersion H.inclusion.hom.hom.left) :
    Function.Surjective (mapPointKernel H.inclusion) := by
  let j := H.inclusion.hom.hom
  letI := hH
  intro p
  let x : Points G.X (CommAlgCat.of k (DualNumber k)) := p.toMul.val
  have hx : Set.range x.left ⊆ Set.range j.left := by
    rintro _ ⟨a, rfl⟩
    obtain ⟨b, rfl⟩ := dualReduction_surjective_on_spectrum (k := k) a
    have h := p.toMul.property
    change (testSpec k).map (dualReduction k).op ≫ x = 1 at h
    have h' := congrArg (fun z : Points G.X (CommAlgCat.of k k) => z.left b) h
    change x.left (((testSpec k).map (dualReduction k).op).left b) =
      (1 : Points G.X (CommAlgCat.of k k)).left b at h'
    rw [h']
    refine ⟨(1 : Points H.group.X (CommAlgCat.of k k)).left b, ?_⟩
    exact congrArg (fun z : Points G.X (CommAlgCat.of k k) => z.left b) (MonObj.one_comp j)
  let z := IsOpenImmersion.lift j.left x.left hx
  have hz : z ≫ j.left = x.left := IsOpenImmersion.lift_fac _ _ _
  let z' : Points H.group.X (CommAlgCat.of k (DualNumber k)) := Over.homMk z (by
    rw [← Over.w j, ← Category.assoc, hz]
    exact Over.w x)
  have hz' : z' ≫ j = x := Over.OverMorphism.ext hz
  have h1 : reduceTangentPoints H.group z' = 1 := by
    haveI : Mono j := Over.mono_of_mono_left _
    apply (cancel_mono j).mp
    change ((testSpec k).map (dualReduction k).op ≫ z') ≫ j = 1 ≫ j
    rw [Category.assoc, hz', MonObj.one_comp]
    exact p.toMul.property
  exact ⟨⟨z', h1⟩, Subtype.ext hz'⟩

private theorem baseChangePoint_map (K : Type u) [Field K] [Algebra k K]
    {G L : GroupScheme k} (f : G ⟶ L) (R : TestAlgebra K)
    (g : GroupPoints ((groupBaseChange k K).obj G) R) :
    baseChangePoint k K L.X R (onPoints ((groupBaseChange k K).map f) R g) =
      onPoints f ((restrictTestAlgebra k K).obj R) (baseChangePoint k K G.X R g) := by
  apply Over.OverMorphism.ext
  change (g.left ≫ ((baseChange k K).map f.hom.hom).left) ≫
      pullback.fst L.X.hom (fieldSpecMap k K) =
    (g.left ≫ pullback.fst G.X.hom (fieldSpecMap k K)) ≫ f.hom.hom.left
  rw [Category.assoc, Category.assoc]
  exact congrArg (g.left ≫ ·) (pullback.lift_fst _ _ _)

private def matrixPointsOver (K : Type u) [Field K] [Algebra k K]
    {G : GroupScheme k} {I : Type u} [Fintype I] [DecidableEq I]
    (l : (groupPointsFunctor k).obj G ≅ StandardGroups.generalLinearPoints k I) :
    (groupPointsFunctor K).obj ((groupBaseChange k K).obj G) ≅
      StandardGroups.generalLinearPoints K I := by
  let e (R : TestAlgebra K) :
      GroupPoints ((groupBaseChange k K).obj G) R ≃* Matrix.GeneralLinearGroup I R :=
    (baseChangePointGroupEquiv K G R).trans
      ((l.app ((restrictTestAlgebra k K).obj R)).groupIsoToMulEquiv)
  refine NatIso.ofComponents (fun R => (e R).toGrpIso) ?_
  intro R S b
  apply GrpCat.ext
  intro g
  let g' := baseChangePoint k K G.X R g
  change (l.hom.app ((restrictTestAlgebra k K).obj S)).hom
    (baseChangePoint k K G.X S (mapPoints b g)) =
      Matrix.GeneralLinearGroup.map b.hom.toRingHom
        ((l.hom.app ((restrictTestAlgebra k K).obj R)).hom g')
  rw [baseChangePointsNaturality k K G.X b g]
  exact (NatTrans.naturality_apply l.hom ((restrictTestAlgebra k K).map b) g')

private theorem baseChangeMatrixCentralizer (K : Type u) [Field K] [Algebra k K]
    {G L : GroupScheme k} {I : Type u} [Fintype I] [DecidableEq I]
    (l : (groupPointsFunctor k).obj L ≅ StandardGroups.generalLinearPoints k I)
    (f : G ⟶ L) (Y : Matrix I I k) (C : ClosedSubgroup G)
    (hc : IsMatrixCentralizer l f Y C) :
    IsMatrixCentralizer (matrixPointsOver K l) ((groupBaseChange k K).map f)
      (Y.map (algebraMap k K))
      (baseChangedSubgroup K C (baseChangeClosedSubgroup k K _ C.isClosedImmersion)) := by
  intro R g
  let a := baseChangePointGroupEquiv K G R
  let b := baseChangePointGroupEquiv K C.group R
  have h := hc ((restrictTestAlgebra k K).obj R) (a g)
  rw [Matrix.map_map]
  change (∃ c : GroupPoints ((groupBaseChange k K).obj C.group) R,
      onPoints ((groupBaseChange k K).map C.inclusion) R c = g) ↔
    Commute ((matrixPointsOver K l).hom.app R
      (onPoints ((groupBaseChange k K).map f) R g)).val
      (Y.map ((algebraMap K R).comp (algebraMap k K)))
  have hm :
      (matrixPointsOver K l).hom.app R (onPoints ((groupBaseChange k K).map f) R g) =
      l.hom.app ((restrictTestAlgebra k K).obj R) (onPoints f _ (a g)) := by
    change (l.hom.app ((restrictTestAlgebra k K).obj R)).hom
      (baseChangePoint k K L.X R (onPoints ((groupBaseChange k K).map f) R g)) = _
    exact congrArg (l.hom.app ((restrictTestAlgebra k K).obj R)).hom (baseChangePoint_map K f R g)
  rw [hm]
  refine Iff.trans ?_ h
  refine ⟨?_, ?_⟩
  · rintro ⟨c, rfl⟩
    exact ⟨b c, (baseChangePoint_map K C.inclusion R c).symm⟩
  · rintro ⟨x, hx⟩
    obtain ⟨c, rfl⟩ := b.surjective x
    refine ⟨c, a.injective ?_⟩
    exact (baseChangePoint_map K C.inclusion R c).trans hx

private theorem matrixDifferential_baseChange (K : Type u) [Field K] [Algebra k K]
    {G L : GroupScheme k} {I : Type u} [Fintype I] [DecidableEq I]
    (l : (groupPointsFunctor k).obj L ≅ StandardGroups.generalLinearPoints k I)
    (f : G ⟶ L) (y : Lie k G) (yK : Lie K ((groupBaseChange k K).obj G))
    (hy : baseChangePoint k K G.X (CommAlgCat.of K (DualNumber K)) yK.toMul.val =
      mapPoints (extendDualNumber K) y.toMul.val) :
    InfinitesimalCommutator.matrixDifferential ((groupBaseChange k K).map f)
      (matrixPointsOver K l) yK =
        (InfinitesimalCommutator.matrixDifferential f l y).map (algebraMap k K) := by
  let R := CommAlgCat.of K (DualNumber K)
  have h := baseChangePoint_map K f R yK.toMul.val
  rw [hy, ← onPoints_mapPoints] at h
  ext i j
  unfold InfinitesimalCommutator.matrixDifferential
  change (((l.hom.app ((restrictTestAlgebra k K).obj R)).hom
      (baseChangePoint k K L.X R (onPoints ((groupBaseChange k K).map f) R yK.toMul.val))).val i j).snd = _
  rw [h]
  have hn := NatTrans.naturality_apply l.hom (extendDualNumber K)
    (onPoints f (CommAlgCat.of k (DualNumber k)) y.toMul.val)
  exact congrArg (fun g : Matrix.GeneralLinearGroup I (DualNumber K) => (g.val i j).snd) hn

/-- Matrix commutation with a Lie vector is commutation with its dual-number
point after the other factor is lifted as a constant. -/
private theorem matrixCommute_iff_dualPointCommute {G L : GroupScheme k}
    {I : Type u} [Fintype I] [DecidableEq I]
    (l : (groupPointsFunctor k).obj L ≅ StandardGroups.generalLinearPoints k I)
    (f : G ⟶ L) (hf : IsClosedImmersion f.hom.hom.left)
    (y : Lie k G) (R : TestAlgebra k) (g : GroupPoints G R) :
    Commute (l.hom.app R (onPoints f R g)).val
        ((InfinitesimalCommutator.matrixDifferential f l y).map (algebraMap k R)) ↔
      Commute (mapPoints (constants R) g : GroupPoints G (CommAlgCat.of k (DualNumber R)))
        (mapPoints (dualMap (CommAlgCat.ofHom (Algebra.ofId k R))) y.toMul.val) := by
  let β := matrixPointMap f l
  let A := CommAlgCat.of k (DualNumber R)
  let a := dualMap (CommAlgCat.ofHom (Algebra.ofId k R))
  let M := (β.app R).hom g
  let yR : GroupPoints G A := mapPoints a y.toMul.val
  let gR : GroupPoints G A := mapPoints (constants R) g
  let P := (β.app A).hom yR
  let Q := (β.app A).hom gR
  let Y := InfinitesimalCommutator.matrixDifferential f l y
  let YR := Y.map (algebraMap k R)
  let m : Matrix I I (DualNumber R) →+* DualNumber (Matrix I I R) := matrixDual
  have hk0 := matrixDual_kernel (mapDualKernel β y)
  have hy0 : matrixDual ((β.app (CommAlgCat.of k (DualNumber k))).hom y.toMul.val).val = (1, Y) :=
    hk0
  have hnat (S T : TestAlgebra k) (b : S ⟶ T) (p : GroupPoints G S) :
      (β.app T).hom (mapPoints b p) =
        Matrix.GeneralLinearGroup.map b.hom.toRingHom ((β.app S).hom p) :=
    NatTrans.naturality_apply β b p
  have hQ : m Q.val = (M.val, 0) := by
    change m ((β.app A).hom (mapPoints (constants R) g)).val = _
    rw [hnat]
    rfl
  have hP : m P.val = (1, YR) := by
    change m ((β.app A).hom (mapPoints a y.toMul.val)).val = _
    rw [hnat]
    apply TrivSqZeroExt.ext <;> ext i j
    · change (algebraMap k R) ((((β.app (CommAlgCat.of k (DualNumber k))).hom
          y.toMul.val).val i j).fst) = (1 : Matrix I I R) i j
      have hx := congrArg (fun z : DualNumber (Matrix I I k) => z.fst i j) hy0
      change (((β.app (CommAlgCat.of k (DualNumber k))).hom
          y.toMul.val).val i j).fst = (1 : Matrix I I k) i j at hx
      rw [hx]
      by_cases h : i = j <;> simp [Matrix.one_apply, h]
    · rfl
  have hm : Function.Injective m := by
    intro B C h
    apply Matrix.ext
    intro i j
    exact TrivSqZeroExt.ext
      (congrArg (fun z : DualNumber (Matrix I I R) => z.fst i j) h)
      (congrArg (fun z : DualNumber (Matrix I I R) => z.snd i j) h)
  have hb : Function.Injective (β.app A).hom :=
    ((l.app A).groupIsoToMulEquiv).injective.comp (onPoints_injective f hf A)
  have hcomm : Commute M.val YR ↔ Commute Q P := by
    change M.val * YR = YR * M.val ↔ Q * P = P * Q
    constructor
    · intro h
      apply Units.ext
      apply hm
      change m (Q.val * P.val) = m (P.val * Q.val)
      rw [map_mul, map_mul, hQ, hP]
      apply TrivSqZeroExt.ext
      · simp
      · simp [h]
    · intro h
      have he := congrArg (fun g : Matrix.GeneralLinearGroup I (DualNumber R) => m g.val) h
      change m (Q.val * P.val) = m (P.val * Q.val) at he
      rw [map_mul, map_mul, hQ, hP] at he
      simpa [DualNumber.snd_mul] using congrArg TrivSqZeroExt.snd he
  change Commute M.val YR ↔ Commute gR yR
  rw [hcomm]
  exact ⟨fun h => hb ((map_mul _ _ _).trans (h.eq.trans (map_mul _ _ _).symm)),
    fun h => h.map (β.app A).hom⟩

private theorem rootPoint_natural {A : RootGroups.AdditiveLine k} {G : GroupScheme k}
    (x : A.group ⟶ G) {R S : TestAlgebra k} (a : R ⟶ S) (b : R) :
    mapPoints a (RootGroups.rootPoint x R b) = RootGroups.rootPoint x S (a.hom b) := by
  unfold mapPoints RootGroups.rootPoint
  rw [← Category.assoc, ← Functor.map_comp, ← op_comp]
  congr 2
  apply Quiver.Hom.unop_inj
  apply CommAlgCat.hom_ext
  apply Polynomial.algHom_ext
  simp

/-- The prescribed scalar action integrates the vanishing differential to the
full scheme root subgroup in the matrix centralizer. -/
private theorem rootSubgroup_le_matrixCentralizer {G L : GroupScheme k}
    {I : Type u} [Fintype I] [DecidableEq I]
    (l : (groupPointsFunctor k).obj L ≅ StandardGroups.generalLinearPoints k I)
    (f : G ⟶ L) (hf : IsClosedImmersion f.hom.hom.left)
    (C T U : ClosedSubgroup G) {A : RootGroups.AdditiveLine k} (x : A.group ≅ U.group)
    (χ : Character T.group) (hx : RootGroups.HasScalarAction T χ (x.hom ≫ U.inclusion))
    (t : Lie k T.group)
    (hχ : characterValue χ (CommAlgCat.of k (DualNumber k)) t.toMul.val = 1)
    (hC : IsMatrixCentralizer l f
      (InfinitesimalCommutator.matrixDifferential f l (mapPointKernel T.inclusion t)) C) :
    IsSubgroupOf U C := by
  let R := CommAlgCat.of k (Polynomial k)
  let S := CommAlgCat.of k (DualNumber R)
  let p := RootGroups.rootPoint (x.hom ≫ U.inclusion) R Polynomial.X
  let a := dualMap (CommAlgCat.ofHom (Algebra.ofId k R))
  have hcomm : Commute
      (mapPoints (constants R) p : GroupPoints G S)
      (mapPoints a (mapPointKernel T.inclusion t).toMul.val) := by
    let u := mapPoints a t.toMul.val
    have hu : characterValue χ S u = 1 := by
      change characterValue χ S (mapPoints a t.toMul.val) = _
      rw [characterValue_natural, hχ]
      exact a.hom.map_one
    have he := hx S u ((constants R).hom Polynomial.X)
    change onPoints T.inclusion S u *
      RootGroups.rootPoint (x.hom ≫ U.inclusion) S ((constants R).hom Polynomial.X) *
        (onPoints T.inclusion S u)⁻¹ =
      RootGroups.rootPoint (x.hom ≫ U.inclusion) S
        (characterValue χ S u * (constants R).hom Polynomial.X) at he
    rw [hu, one_mul, ← rootPoint_natural (x.hom ≫ U.inclusion) (constants R),
      ← onPoints_mapPoints] at he
    exact (mul_inv_eq_iff_eq_mul.mp he).symm
  have hmp := (matrixCommute_iff_dualPointCommute l f hf
    (mapPointKernel T.inclusion t) R p).mpr hcomm
  obtain ⟨c, hc⟩ := (hC R p).mpr hmp
  have hp : p = (x.hom ≫ U.inclusion).hom.hom := by
    change (testSpec k).map (CommAlgCat.ofHom
      (Polynomial.aeval Polynomial.X : Polynomial k →ₐ[k] Polynomial k)).op ≫
        (x.hom ≫ U.inclusion).hom.hom = _
    have hpoly : (Polynomial.aeval Polynomial.X : Polynomial k →ₐ[k] Polynomial k) =
        AlgHom.id k (Polynomial k) := by
      apply Polynomial.algHom_ext
      simp
    rw [hpoly, CommAlgCat.ofHom_id]
    exact congrArg (fun q : A.group.X ⟶ A.group.X => q ≫ (x.hom ≫ U.inclusion).hom.hom)
      ((testSpec k).map_id (op R)) |>.trans (Category.id_comp _)
  have hcf : c ≫ C.inclusion.hom.hom = (x.hom ≫ U.inclusion).hom.hom := hc.trans hp
  obtain ⟨j, hj⟩ := factor_group_through_subgroup C (x.hom ≫ U.inclusion) c hcf
  exact ⟨x.inv ≫ j, by rw [Category.assoc, hj, Iso.inv_hom_id_assoc]⟩

/-- This tests the Lie commutator by taking the coefficient of the
square-zero generator in the original faithful matrix representation. -/
private theorem commute_matrixDifferentials_iff {G L : GroupScheme k}
    {I : Type u} [Fintype I] [DecidableEq I]
    (l : (groupPointsFunctor k).obj L ≅ StandardGroups.generalLinearPoints k I)
    (f : G ⟶ L) (x y : Lie k G) :
    Commute (InfinitesimalCommutator.matrixDifferential f l x)
      (InfinitesimalCommutator.matrixDifferential f l y) ↔
    Commute (l.hom.app (CommAlgCat.of k (DualNumber k))
      (onPoints f (CommAlgCat.of k (DualNumber k)) x.toMul.val)).val
      ((InfinitesimalCommutator.matrixDifferential f l y).map (algebraMap k (DualNumber k))) := by
  let P := (l.hom.app (CommAlgCat.of k (DualNumber k))
    (onPoints f (CommAlgCat.of k (DualNumber k)) x.toMul.val)).val
  let X := InfinitesimalCommutator.matrixDifferential f l x
  let Y := InfinitesimalCommutator.matrixDifferential f l y
  let Q := Y.map (algebraMap k (DualNumber k))
  let m : Matrix I I (DualNumber k) →+* DualNumber (Matrix I I k) := matrixDual
  have hp : m P = (1, X) := matrixDual_kernel (mapDualKernel (matrixPointMap f l) x)
  have hq : m Q = (Y, 0) := rfl
  have hm : Function.Injective m := by
    intro B C h
    apply Matrix.ext
    intro i j
    exact TrivSqZeroExt.ext
      (congrArg (fun z : DualNumber (Matrix I I k) => z.fst i j) h)
      (congrArg (fun z : DualNumber (Matrix I I k) => z.snd i j) h)
  change X * Y = Y * X ↔ P * Q = Q * P
  rw [← hm.eq_iff, map_mul, map_mul, hp, hq]
  constructor
  · intro h
    apply TrivSqZeroExt.ext
    · simp
    · simp [h]
  · intro h
    simpa using congrArg TrivSqZeroExt.snd h
private theorem lie_of_subgroupProduct {G : GroupScheme k} (U T : ClosedSubgroup G)
    (h : IsIso (CocharacterDynamics.multiplyFactors U.inclusion T.inclusion))
    (v : Lie k G) : ∃ u : Lie k U.group, ∃ t : Lie k T.group,
      v = mapPointKernel U.inclusion u + mapPointKernel T.inclusion t := by
  let R := CommAlgCat.of k (DualNumber k)
  let B := CommAlgCat.of k k
  let m := CocharacterDynamics.multiplyFactors U.inclusion T.inclusion
  letI : IsIso m := h
  let vx : Points G.X R := v.toMul.val
  let z : Points (U.group.X ⊗ T.group.X) R := vx ≫ inv m
  let p := z ≫ fst U.group.X T.group.X
  let q := z ≫ snd U.group.X T.group.X
  have hfac {X : SchemeOver k} (a : X ⟶ U.group.X) (b : X ⟶ T.group.X) :
      lift a b ≫ m = (a ≫ U.inclusion.hom.hom) * (b ≫ T.inclusion.hom.hom) := by
    simp only [m, CocharacterDynamics.multiplyFactors, MonObj.comp_mul,
      lift_fst_assoc, lift_snd_assoc]
  have hred : mapPoints (dualReduction k) z =
      (lift (1 : Points U.group.X B) (1 : Points T.group.X B)) := by
    apply (cancel_mono m).mp
    change (((testSpec k).map (dualReduction k).op ≫ (vx ≫ inv m)) ≫ m) =
      lift (1 : Points U.group.X B) (1 : Points T.group.X B) ≫ m
    simp only [Category.assoc, IsIso.inv_hom_id, Category.comp_id, hfac, MonObj.one_comp, mul_one]
    exact v.toMul.property
  have hp : reduceTangentPoints U.group p = 1 := by
    change (testSpec k).map (dualReduction k).op ≫ z ≫ fst U.group.X T.group.X = 1
    rw [← Category.assoc, ← show mapPoints (dualReduction k) z =
      (testSpec k).map (dualReduction k).op ≫ z from rfl, hred, lift_fst]
  have hq : reduceTangentPoints T.group q = 1 := by
    change (testSpec k).map (dualReduction k).op ≫ z ≫ snd U.group.X T.group.X = 1
    rw [← Category.assoc, ← show mapPoints (dualReduction k) z =
      (testSpec k).map (dualReduction k).op ≫ z from rfl, hred, lift_snd]
  refine ⟨⟨p, hp⟩, ⟨q, hq⟩, Subtype.ext ?_⟩
  change vx = (p ≫ U.inclusion.hom.hom) * (q ≫ T.inclusion.hom.hom)
  have hl : lift p q = z := by
    apply CartesianMonoidalCategory.hom_ext
    · exact lift_fst p q
    · exact lift_snd p q
  rw [← hfac, hl]
  change vx = (vx ≫ inv m) ≫ m
  rw [Category.assoc, IsIso.inv_hom_id, Category.comp_id]

private theorem matrixDifferential_add {G L : GroupScheme k}
    {I : Type u} [Fintype I] [DecidableEq I] (f : G ⟶ L)
    (l : (groupPointsFunctor k).obj L ≅ StandardGroups.generalLinearPoints k I)
    (x y : Lie k G) :
    InfinitesimalCommutator.matrixDifferential f l (x + y) =
      InfinitesimalCommutator.matrixDifferential f l x +
        InfinitesimalCommutator.matrixDifferential f l y := by
  simp only [matrixDifferential_eq, map_add, matrixCoefficient_add]

private theorem matrixDifferential_comp {G H L : GroupScheme k}
    {I : Type u} [Fintype I] [DecidableEq I] (a : G ⟶ H) (f : H ⟶ L)
    (l : (groupPointsFunctor k).obj L ≅ StandardGroups.generalLinearPoints k I)
    (v : Lie k G) :
    InfinitesimalCommutator.matrixDifferential (a ≫ f) l v =
      InfinitesimalCommutator.matrixDifferential f l (mapPointKernel a v) := by
  have h := (lieFunctoriality k).2.2 G H L a f v
  unfold InfinitesimalCommutator.matrixDifferential
  rw [h]

private theorem matrixDifferential_zero {G L : GroupScheme k}
    {I : Type u} [Fintype I] [DecidableEq I] (f : G ⟶ L)
    (l : (groupPointsFunctor k).obj L ≅ StandardGroups.generalLinearPoints k I) :
    InfinitesimalCommutator.matrixDifferential f l 0 = 0 := by
  let D := InfinitesimalCommutator.matrixDifferential f l (0 : Lie k G)
  have h : D = D + D := by simpa only [zero_add] using matrixDifferential_add f l 0 0
  apply add_left_cancel (a := D)
  rw [add_zero, ← h]
/-- Applying an invariant derivation to the coefficients of a coaction gives
the matrix of the induced tangent operator in any basis. -/
private theorem coactionOperator_in_basis {V I : Type u} [AddCommGroup V] [Module k V]
    [Fintype I] [DecidableEq I] (A : HopfAlgebraCategory k) (b : Module.Basis I k V)
    (D : InvariantDerivation A) (ρ : RightComodule k A V) :
    LinearMap.toMatrixAlgEquiv b (coactionOperator A D ρ) =
      matrixAction A (RationalRepresentations.coefficients A b ρ) D := by
  ext i j
  rw [LinearMap.toMatrixAlgEquiv_apply]
  change b.repr ((TensorProduct.rid k V)
    (((Coalgebra.counit (R := k)).comp D.val.toLinearMap).lTensor V (ρ.coaction (b j)))) i = _
  rw [RationalRepresentations.coaction_apply_basis A b ρ j]
  simp [matrixAction, Finsupp.single_apply]

private theorem matrixDifferential_unipotent_isNilpotent
    (U : AffineAlgebraicGroup k) (hU : IsUnipotent U)
    {I : Type u} [Fintype I] [DecidableEq I] {L : GroupScheme k}
    (l : (groupPointsFunctor k).obj L ≅ StandardGroups.generalLinearPoints k I)
    (f : U.val ⟶ L) (y : Lie k U.val) :
    IsNilpotent (Matrix.toLinAlgEquiv' (InfinitesimalCommutator.matrixDifferential f l y)) := by
  rcases subsingleton_or_nontrivial (I → k) with hv | hv
  · letI := hv
    exact ⟨1, Subsingleton.elim _ _⟩
  letI := hv
  obtain ⟨A, ⟨e⟩, hA⟩ := hU
  let U' : AffineGroupCategory k := ⟨U.val, U.property.1⟩
  let e' := hopfSpecPointIso A ≪≫ (groupPointsFunctor k).mapIso e
  let t := tangentComparison A U.val e'
  obtain ⟨D, rfl⟩ := t.surjective y
  let M := RationalRepresentations.universalMatrix A U' L e' l f
  let hM := universalMatrix_coaction A U' e' L l f
  let ρ := RationalRepresentations.coactionOfMatrix A (Pi.basisFun k I) M hM
  obtain ⟨b, hb⟩ := (Unipotent.hasFullFlags_of_invariants A hA) (I → k) ρ
  let W := coactionOperator A D ρ
  let N := matrixAction A (RationalRepresentations.coefficients A b ρ) D
  have hn : LinearMap.toMatrixAlgEquiv b W = N := coactionOperator_in_basis A b D ρ
  have htri : N.IsUpperTriangular := by
    intro i j hij
    change Coalgebra.counit (R := k) (D.val (RationalRepresentations.coefficients A b ρ i j)) = 0
    rw [hb.1 hij, map_zero, map_zero]
  have hdiag (i : Index (Module.finrank k (I → k))) : N i i = 0 := by
    change Coalgebra.counit (R := k) (D.val (RationalRepresentations.coefficients A b ρ i i)) = 0
    rw [hb.2 i, Derivation.map_one_eq_zero, map_zero]
  have hpoly : N.charpoly = Polynomial.X ^ Fintype.card (Index.{u} (Module.finrank k (I → k))) := by
    rw [Matrix.charpoly_of_isUpperTriangular N htri]
    simp [hdiag]
  have hpow := N.aeval_self_charpoly
  rw [hpoly, map_pow, Polynomial.aeval_X] at hpow
  have hnil : IsNilpotent W := by
    refine ⟨Fintype.card (Index.{u} (Module.finrank k (I → k))), ?_⟩
    apply (LinearMap.toMatrixAlgEquiv b).injective
    rw [map_pow, hn, map_zero]
    exact hpow
  have h := coactionOperator_matrix A D M hM
  have hd : InfinitesimalCommutator.matrixDifferential f l (t D) = matrixAction A M D :=
    tangentComparison_matrix A U' e' L l f D
  rw [hd, ← h]
  exact hnil
/-- A split torus has a weight basis even in positive characteristic, and
differentiation acts diagonally in that same basis. -/
private theorem matrixDifferential_splitTorus_isSemisimple
    (T : AffineAlgebraicGroup k) (hT : IsSplitTorus T.val)
    {I : Type u} [Fintype I] [DecidableEq I] {L : GroupScheme k}
    (l : (groupPointsFunctor k).obj L ≅ StandardGroups.generalLinearPoints k I)
    (f : T.val ⟶ L) (y : Lie k T.val) :
    Module.End.IsSemisimple
      (Matrix.toLinAlgEquiv' (InfinitesimalCommutator.matrixDifferential f l y)) := by
  classical
  obtain ⟨r, ⟨e⟩⟩ := splitPresentation hT
  let M := CharacterDescent.StandardLattice.{u} r
  let A := groupAlgebra k M
  let T' : AffineGroupCategory k := ⟨T.val, T.property.1⟩
  let e' := hopfSpecPointIso A ≪≫ (groupPointsFunctor k).mapIso e
  let t := tangentComparison A T.val e'
  obtain ⟨D, rfl⟩ := t.surjective y
  let Mtx := RationalRepresentations.universalMatrix A T' L e' l f
  let hMtx := universalMatrix_coaction A T' e' L l f
  let ρ := RationalRepresentations.coactionOfMatrix A (Pi.basisFun k I) Mtx hMtx
  let W := coactionOperator A D ρ
  obtain ⟨J, hJ, b, w, hb⟩ := DiagonalizableFixedLocus.existsWeightBasis (M := M) ρ
  letI : Fintype J := Fintype.ofFinite J
  let c : J → k := fun i => Coalgebra.counit (R := k) (D.val (MonoidAlgebra.of k M (w i)))
  have heig (j : J) : W (b j) = c j • b j := by
    have hh := WeightDecomposition.mem_weightSpace.mp (hb j)
    change (TensorProduct.rid k (I → k))
      (((Coalgebra.counit (R := k)).comp D.val.toLinearMap).lTensor (I → k)
        (ρ.coaction (b j))) = _
    rw [hh]
    rfl
  let v := Finset.univ.image c
  let P : Polynomial k := ∏ a ∈ v, (Polynomial.X - Polynomial.C a)
  have hP : P.Separable :=
    Polynomial.separable_prod_X_sub_C_iff'.mpr (fun _ _ _ _ he => he)
  have hw : Polynomial.aeval W P = 0 := by
    apply b.ext
    intro j
    rw [Module.End.aeval_apply_of_mem_apply_eq_smul (heig j)]
    have hj : c j ∈ v := Finset.mem_image_of_mem c (Finset.mem_univ j)
    have hz : P.eval (c j) = 0 := by
      change Polynomial.eval (c j) (∏ a ∈ v, _) = _
      rw [Polynomial.eval_prod]
      apply Finset.prod_eq_zero hj
      simp
    simp [hz]
  have h := coactionOperator_matrix A D Mtx hMtx
  have hd : InfinitesimalCommutator.matrixDifferential f l (t D) = matrixAction A Mtx D :=
    tangentComparison_matrix A T' e' L l f D
  rw [hd, ← h]
  exact Module.End.isSemisimple_of_squarefree_aeval_eq_zero hP.squarefree hw
/-- A semisimple Lie direction fixed by the whole connected group lies in the
Lie algebra of each maximal torus of that group. -/
private theorem semisimpleCentralLie_in_maximalTorus [IsAlgClosed k]
    (B : AffineAlgebraicGroup k) (hsB : Smooth B.val.X.hom) (hcB : ConnectedSpace B.val.X.left)
    (T : ClosedSubgroup B.val) (hT : IsMaximalTorus T)
    {I : Type u} [Fintype I] [DecidableEq I] (L : AffineGroupCategory k)
    (l : (groupPointsFunctor k).obj L.val ≅ StandardGroups.generalLinearPoints k I)
    (f : B.val ⟶ L.val) (hf : IsClosedImmersion f.hom.hom.left)
    (y : Lie k B.val)
    (hy : Module.End.IsSemisimple
      (Matrix.toLinAlgEquiv' (InfinitesimalCommutator.matrixDifferential f l y)))
    (hcentral : ∀ (R : TestAlgebra k) (g : GroupPoints B.val R),
      Commute (l.hom.app R (onPoints f R g)).val
        ((InfinitesimalCommutator.matrixDifferential f l y).map (algebraMap k R))) :
    y ∈ CocharacterDynamics.lieImage T := by
  let A := closedSubgroupAlgebraicGroup T
  have hweight : y ∈ adjointWeightVectors T 1 := by
    intro R t
    have h := (matrixCommute_iff_dualPointCommute l f hf y R
      (onPoints T.inclusion R t)).mp (hcentral R _)
    have h1 : scale R 1 = 𝟙 _ := by
      apply CommAlgCat.hom_ext
      apply AlgHom.ext
      intro z
      exact TrivSqZeroExt.ext rfl (one_mul z.snd)
    dsimp only
    rw [characterValue_one, h1]
    let S := CommAlgCat.of k (DualNumber R)
    let a := dualMap (CommAlgCat.ofHom (Algebra.ofId k R))
    let p : Points B.val.X S := mapPoints a y.toMul.val
    have hpid : mapPoints (𝟙 S) p = p := by
      change (testSpec k).map (𝟙 (op S)) ≫ p = p
      exact (congrArg (· ≫ p) ((testSpec k).map_id (op S))).trans (Category.id_comp p)
    change (mapPoints (constants R) (onPoints T.inclusion R t) : GroupPoints B.val S) *
      p * (mapPoints (constants R) (onPoints T.inclusion R t))⁻¹ = mapPoints (𝟙 S) p
    rw [hpid]
    exact mul_inv_eq_iff_eq_mul.mpr h.eq
  have hcent := (zeroWeightVectors_iff_centralizes T A.property.1 y).mp hweight
  obtain ⟨C, hC, hsC, hcC, hsol, _, j, hjc, Q, q, hj, hq, hu⟩ :=
    TorusFreeUnipotent.maximalTorusCentralizer B hsB hcB T hT
  have hyC : y ∈ CocharacterDynamics.lieImage C := by
    rw [CocharacterDynamics.centralizerLieInvariants T.inclusion C hC]
    exact (isFixedBy_conjugation_iff T.inclusion _).mpr hcent
  obtain ⟨v, hv⟩ := hyC
  let Z := closedSubgroupAlgebraicGroup C
  let V : ClosedSubgroup Z.val := ⟨T.group, j, hjc⟩
  have hV : IsMaximalTorus V := by
    apply local_maximal_of_ambient C V
    have hh : subgroupOfSubgroup C V = T := by
      change (⟨T.group, j ≫ C.inclusion, _⟩ : ClosedSubgroup B.val) = T
      cases T
      congr
    exact hh.symm ▸ hT
  letI : GeometricallyConnected Z.val.X.hom := hcC
  have hconn : ConnectedSpace Z.val.X.left :=
    GeometricallyConnected.connectedSpace_of_subsingleton Z.val.X.hom
  obtain ⟨U, D, p, hU, _, _, _, hsplit⟩ :=
    GeometricTorusSplitting.splitting Z hsC hconn hsol
  have hprod : IsIso (CocharacterDynamics.multiplyFactors U.inclusion V.inclusion) :=
    (hsplit V).2 ((solvable_maximal_torus_iff Z V).mpr hV)
  obtain ⟨u, t, hut⟩ := lie_of_subgroupProduct U V hprod v
  let uB := mapPointKernel (U.inclusion ≫ C.inclusion) u
  let tB := mapPointKernel T.inclusion t
  have hsum : y = uB + tB := by
    have hu' := (lieFunctoriality k).2.2 U.group C.group B.val U.inclusion C.inclusion u
    have ht' := (lieFunctoriality k).2.2 V.group C.group B.val V.inclusion C.inclusion t
    have ht'' : mapPointKernel (V.inclusion ≫ C.inclusion) t = tB := by
      change mapPointKernel (j ≫ C.inclusion) t = _
      exact congrArg (fun a => mapPointKernel a t) hj
    calc
      y = mapPointKernel C.inclusion v := hv.symm
      _ = mapPointKernel C.inclusion (mapPointKernel U.inclusion u + mapPointKernel V.inclusion t) :=
        congrArg (mapPointKernel C.inclusion) hut
      _ = _ := (map_add (mapPointKernel C.inclusion) _ _).trans
        (congrArg₂ (· + ·) hu'.symm (ht'.symm.trans ht''))
  let Y := Matrix.toLinAlgEquiv' (InfinitesimalCommutator.matrixDifferential f l y)
  let YU := Matrix.toLinAlgEquiv' (InfinitesimalCommutator.matrixDifferential f l uB)
  let YT := Matrix.toLinAlgEquiv' (InfinitesimalCommutator.matrixDifferential f l tB)
  have hY : Y = YU + YT := by
    dsimp only [Y, YU, YT]
    rw [hsum, matrixDifferential_add, map_add]
  have hUT : IsNilpotent YU := by
    change IsNilpotent (Matrix.toLinAlgEquiv'
      (InfinitesimalCommutator.matrixDifferential f l
        (mapPointKernel (U.inclusion ≫ C.inclusion) u)))
    rw [← matrixDifferential_comp]
    exact matrixDifferential_unipotent_isNilpotent
      (closedSubgroupAlgebraicGroup (G := Z) U) hU.2.2.2.1 l _ u
  have hTor : Module.End.IsSemisimple YT := by
    change Module.End.IsSemisimple (Matrix.toLinAlgEquiv'
      (InfinitesimalCommutator.matrixDifferential f l (mapPointKernel T.inclusion t)))
    rw [← matrixDifferential_comp]
    exact matrixDifferential_splitTorus_isSemisimple A
      (split_of_torus ((isTorus_iff_coordinates A).mp hT.1)) l _ t
  have hcTY : Commute YT Y :=
    ((commute_matrixDifferentials_iff l f tB y).mpr (hcentral _ tB.toMul.val)).map
      (Matrix.toLinAlgEquiv'.toRingHom)
  have hsemU : Module.End.IsSemisimple YU := by
    have h' : Y - YT = YU := by rw [hY, add_sub_cancel_right]
    exact h' ▸ Module.End.IsSemisimple.sub_of_commute hcTY.symm hy hTor
  have hzero := Module.End.eq_zero_of_isNilpotent_isSemisimple hUT hsemU
  have huB : uB = 0 := by
    apply matrixDifferential_injective f l hf
    apply Matrix.toLinAlgEquiv'.injective
    change YU = Matrix.toLinAlgEquiv' (InfinitesimalCommutator.matrixDifferential f l 0)
    rw [hzero]
    simp [matrixDifferential_zero]
  exact ⟨t, by rw [hsum, huB, zero_add]⟩

/-- A nonzero weight vector separates the scalar acting on its dual-number
extension, even if the test algebra has nilpotents. -/
private theorem characterValue_eq_one_of_nonzero_fixedWeight
    (G : AffineAlgebraicGroup k) (T : ClosedSubgroup G.val) (χ : Character T.group)
    (v : Lie k G.val) (hv : v ∈ adjointWeightVectors T χ) (hne : v ≠ 0)
    (R : TestAlgebra k) (t : GroupPoints T.group R)
    (hfix : Commute
      (mapPoints (constants R) (onPoints T.inclusion R t) :
        GroupPoints G.val (CommAlgCat.of k (DualNumber R)))
      (mapPoints (dualMap (CommAlgCat.ofHom (Algebra.ofId k R))) v.toMul.val)) :
    characterValue χ R t = 1 := by
  let s := identityLieStructure G
  letI := s.lieRing
  letI := s.lieAlgebra
  obtain ⟨n, b, C, _, _, _, _, _, _⟩ := adjointRepresentation k G s
  let a := CommAlgCat.ofHom (Algebra.ofId k R)
  let x : ULift.{u} (Fin n) → R := fun j => a.hom (b.equivFun v j)
  let r := characterValue χ R t
  have hp : (C.equiv R x).toMul.val = mapPoints (dualMap a) v.toMul.val :=
    (C.naturality a (b.equivFun v)).trans
      (congrArg (mapPoints (dualMap a)) (C.at_base v))
  have hnv : ∃ j, b.equivFun v j ≠ 0 := by
    by_contra h
    push Not at h
    apply hne
    refine (b.equivFun.injective ((funext h).trans b.equivFun.map_zero.symm)).trans ?_
    exact (canonicalZero_eq s).symm
  obtain ⟨j, hj⟩ := hnv
  have heq : mapPoints (scale R r) (C.equiv R x).toMul.val = (C.equiv R x).toMul.val := by
    rw [hp]
    exact (hv R t).symm.trans (mul_inv_eq_iff_eq_mul.mpr hfix.eq)
  have hb : r • x = x := by
    apply (C.equiv R).injective
    apply Subtype.ext
    exact (C.smul R r x).trans heq
  have hj' : r * x j = 1 * x j := (congrFun hb j).trans (one_mul _).symm
  have hu : IsUnit (x j) := (isUnit_iff_ne_zero.mpr hj).map a.hom.toMonoidHom
  exact hu.mul_right_cancel hj'

private theorem subgroupOf_of_points {G : GroupScheme k}
    (A B : ClosedSubgroup G) (hA : IsAffine A.group.X.left)
    (h : ∀ (R : TestAlgebra k) (a : GroupPoints A.group R),
      ∃ b : GroupPoints B.group R, onPoints B.inclusion R b = onPoints A.inclusion R a) :
    IsSubgroupOf A B := by
  obtain ⟨j, hj⟩ := sections_factor_of_affine B hA A.inclusion.hom.hom h
  exact factor_group_through_subgroup B A.inclusion j hj

private theorem matrixCentralizer_contains_its_direction
    {G L : GroupScheme k} {I : Type u} [Fintype I] [DecidableEq I]
    (l : (groupPointsFunctor k).obj L ≅ StandardGroups.generalLinearPoints k I)
    (f : G ⟶ L) (y : Lie k G) (C : ClosedSubgroup G)
    (hC : IsMatrixCentralizer l f (InfinitesimalCommutator.matrixDifferential f l y) C) :
    y ∈ CocharacterDynamics.lieImage C := by
  let R := CommAlgCat.of k (DualNumber k)
  have h := (commute_matrixDifferentials_iff l f y y).mp (Commute.refl _)
  obtain ⟨z, hz⟩ := (hC R y.toMul.val).mpr h
  have hz₁ : reduceTangentPoints C.group z = 1 := by
    apply onPoints_injective C.inclusion C.isClosedImmersion (CommAlgCat.of k k)
    change onPoints C.inclusion (CommAlgCat.of k k) (mapPoints (dualReduction k) z) =
      onPoints C.inclusion (CommAlgCat.of k k) 1
    rw [← onPoints_mapPoints, show onPoints C.inclusion R z = y.toMul.val from hz, map_one]
    exact y.toMul.property
  exact ⟨⟨z, hz₁⟩, Subtype.ext hz⟩

private theorem reducedIdentityComponent_of_open_closed
    {G : GroupScheme k} (H : ClosedSubgroup G) (hO : IsOpenImmersion H.inclusion.hom.hom.left)
    (hs : Smooth H.group.X.hom) (hc : ConnectedSpace H.group.X.left) :
    IsReducedIdentityComponent H := by
  letI := hs
  letI := hc
  letI := H.isClosedImmersion
  letI := hO
  refine ⟨isReduced_of_smooth_over_field H.group.X.hom, ?_⟩
  have hcl : IsClopen (Set.range H.inclusion.hom.hom.left) :=
    ⟨H.inclusion.hom.hom.left.isClosedEmbedding.isClosed_range,
      H.inclusion.hom.hom.left.isOpenEmbedding.isOpen_range⟩
  have hunit : η[G.X].left (IsLocalRing.closedPoint k) ∈
      Set.range H.inclusion.hom.hom.left := by
    refine ⟨η[H.group.X].left (IsLocalRing.closedPoint k), ?_⟩
    rw [← Scheme.Hom.comp_apply, ← Over.comp_left, IsMonHom.one_hom]
  exact ((isConnected_range H.inclusion.hom.hom.left.continuous).subset_connectedComponent
    hunit).antisymm (hcl.connectedComponent_subset hunit)

private theorem maximalTorus_exists [IsAlgClosed k]
    (G : AffineAlgebraicGroup k) (hs : Smooth G.val.X.hom) (hc : ConnectedSpace G.val.X.left) :
    ∃ T : ClosedSubgroup G.val, IsMaximalTorus T := by
  obtain ⟨B, hB⟩ := GeometricBorelConjugacy.borelExists G hs hc
  let A := closedSubgroupAlgebraicGroup B
  obtain ⟨U, D, p, hU, hp, hD, ⟨T, hT⟩, _⟩ :=
    GeometricTorusSplitting.splitting A hB.1.1 hB.1.2.1 hB.1.2.2
  exact ⟨subgroupOfSubgroup B T, (MaximalToriConjugate.borelMaximalTorusIff G hs hc B hB T).mp
    ((solvable_maximal_torus_iff A T).mp hT)⟩

private theorem torusOfCentralizer_maximal [IsAlgClosed k]
    (G : AffineAlgebraicGroup k) {L : GroupScheme k} {I : Type u} [Fintype I] [DecidableEq I]
    (l : (groupPointsFunctor k).obj L ≅ StandardGroups.generalLinearPoints k I)
    (f : G.val ⟶ L) (hf : IsClosedImmersion f.hom.hom.left)
    (C : ClosedSubgroup G.val) (H : ClosedSubgroup C.group)
    (hH : IsReducedIdentityComponent H)
    (T : ClosedSubgroup H.group) (hT : IsMaximalTorus T)
    (t : Lie k T.group)
    (hC : IsMatrixCentralizer l f
      (InfinitesimalCommutator.matrixDifferential f l
        (mapPointKernel (T.inclusion ≫ H.inclusion ≫ C.inclusion) t)) C) :
    IsMaximalTorus (subgroupOfSubgroup (subgroupOfSubgroup C H) T) := by
  let D := subgroupOfSubgroup C H
  let S := subgroupOfSubgroup D T
  refine ⟨hT.1, ?_⟩
  intro U hU hSU
  let A := closedSubgroupAlgebraicGroup U
  obtain ⟨j, hj⟩ := hSU
  let v := mapPointKernel j t
  have hv : mapPointKernel U.inclusion v = mapPointKernel S.inclusion t := by
    exact ((lieFunctoriality k).2.2 T.group U.group G.val j U.inclusion t).symm.trans
      (congrArg (fun m => mapPointKernel m t) hj)
  have hUC : IsSubgroupOf U C := by
    apply subgroupOf_of_points U C A.property.1
    intro R u
    apply (hC R _).mpr
    change Commute _ ((InfinitesimalCommutator.matrixDifferential f l
      (mapPointKernel S.inclusion t)).map (algebraMap k R))
    rw [← hv]
    apply (matrixCommute_iff_dualPointCommute l f hf (mapPointKernel U.inclusion v) R _).mpr
    let a := dualMap (CommAlgCat.ofHom (Algebra.ofId k R))
    let S' := CommAlgCat.of k (DualNumber R)
    change Commute (mapPoints (constants R) (onPoints U.inclusion R u))
      (mapPoints a (onPoints U.inclusion (CommAlgCat.of k (DualNumber k)) v.toMul.val))
    rw [onPoints_mapPoints, onPoints_mapPoints]
    letI : IsCommMonObj U.group.X := torus_commutative A hU
    have hc : Commute ((mapPoints (constants R) u) : GroupPoints U.group S')
        (mapPoints a v.toMul.val) := mul_comm _ _
    exact hc.map (onPoints U.inclusion S')
  obtain ⟨u, hu⟩ := hUC
  obtain ⟨hsU, hcU, _⟩ := torus_smooth_connected_solvable A hU
  obtain ⟨i, hi⟩ := factors_reduced_component H hH u hsU hcU
  have hiD : i ≫ D.inclusion = U.inclusion := by
    change i ≫ H.inclusion ≫ C.inclusion = U.inclusion
    rw [← Category.assoc, hi, hu]
  let V : ClosedSubgroup H.group := ⟨U.group, i, factor_closed hiD⟩
  have htV : IsSubgroupOf T V := by
    refine ⟨j, ?_⟩
    letI := inclusion_mono D
    apply (cancel_mono D.inclusion).mp
    change (j ≫ i) ≫ D.inclusion = S.inclusion
    rw [Category.assoc, hiD, hj]
  obtain ⟨w, hw⟩ := hT.2 V hU htV
  refine ⟨w, ?_⟩
  change w ≫ T.inclusion ≫ D.inclusion = U.inclusion
  exact (Category.assoc _ _ _).symm.trans (congrArg (· ≫ D.inclusion) hw |>.trans hiD)

private theorem characterValue_inv_eq_one {T : GroupScheme k} (χ : Character T)
    (R : TestAlgebra k) (t : GroupPoints T R) (h : characterValue χ R t = 1) :
    characterValue χ⁻¹ R t = 1 := by
  let e := DiagonalizableGroups.multiplicativeGroupIso k
  let m := StandardGroups.multiplicativeGroupPointsIso k
  let f := (m.hom.app R).hom.comp (onPoints e.hom R)
  have hp : onPoints χ⁻¹ R t = (onPoints χ R t)⁻¹ := by
    change t ≫ (χ.hom.hom)⁻¹ = (t ≫ χ.hom.hom)⁻¹
    exact GrpObj.comp_inv t χ.hom.hom
  have ha : f (onPoints χ R t) = 1 := by
    apply Units.ext
    exact (characterValue_standard χ R t).symm.trans h
  rw [characterValue_standard]
  change (f (onPoints χ⁻¹ R t)).val = 1
  rw [hp, map_inv, ha, inv_one]
  rfl

private theorem rootSubgroup_le_component_of_character
    (G : AffineAlgebraicGroup k) {L : GroupScheme k} {I : Type u} [Fintype I] [DecidableEq I]
    (l : (groupPointsFunctor k).obj L ≅ StandardGroups.generalLinearPoints k I)
    (f : G.val ⟶ L) (hf : IsClosedImmersion f.hom.hom.left)
    (C : ClosedSubgroup G.val) (H : ClosedSubgroup C.group) (hH : IsReducedIdentityComponent H)
    (T : ClosedSubgroup G.val) (t : Lie k T.group)
    (hC : IsMatrixCentralizer l f
      (InfinitesimalCommutator.matrixDifferential f l (mapPointKernel T.inclusion t)) C)
    (χ : Character T.group) (hχ : characterValue χ (CommAlgCat.of k (DualNumber k)) t.toMul.val = 1)
    (U : ClosedSubgroup G.val) (hu : IsRootSubgroup T U χ)
    {A : RootGroups.AdditiveLine k} (x : A.group ≅ U.group)
    (hx : RootGroups.HasScalarAction T χ (x.hom ≫ U.inclusion)) :
    IsSubgroupOf U (subgroupOfSubgroup C H) := by
  obtain ⟨j, hj⟩ := rootSubgroup_le_matrixCentralizer l f hf C T U x χ hx t hχ hC
  let e := ((Grp.forget (SchemeOver k)) ⋙ Over.forget _).mapIso x
  have hc : ConnectedSpace U.group.X.left :=
    e.hom.homeomorph.connectedSpace_iff.mp
      (inferInstanceAs (ConnectedSpace (PrimeSpectrum (Polynomial k))))
  obtain ⟨i, hi⟩ := factors_reduced_component H hH j hu.1 hc
  exact ⟨i, (Category.assoc _ _ _).symm.trans (congrArg (· ≫ C.inclusion) hi |>.trans hj)⟩

private theorem centralizerRootCharacters
    (G : AffineAlgebraicGroup k) {L : GroupScheme k} {I : Type u} [Fintype I] [DecidableEq I]
    (l : (groupPointsFunctor k).obj L ≅ StandardGroups.generalLinearPoints k I)
    (f : G.val ⟶ L) (hf : IsClosedImmersion f.hom.hom.left)
    (C : ClosedSubgroup G.val) (H : ClosedSubgroup C.group)
    (T : ClosedSubgroup G.val) (t : Lie k T.group)
    (hC : IsMatrixCentralizer l f
      (InfinitesimalCommutator.matrixDifferential f l (mapPointKernel T.inclusion t)) C)
    (χ : Character T.group) (hχ : χ ∈ subgroupRoots T (subgroupOfSubgroup C H)) :
    characterValue χ (CommAlgCat.of k (DualNumber k)) t.toMul.val = 1 := by
  obtain ⟨_, v, hv, ⟨w, hw⟩, hne⟩ := hχ
  let y := mapPointKernel T.inclusion t
  let R := CommAlgCat.of k (DualNumber k)
  have hmem : ∃ z : GroupPoints C.group R, onPoints C.inclusion R z = v.toMul.val := by
    refine ⟨(mapPointKernel H.inclusion w).toMul.val, ?_⟩
    have h := (lieFunctoriality k).2.2 H.group C.group G.val H.inclusion C.inclusion w
    exact congrArg (fun a : Lie k G.val => a.toMul.val) (h.symm.trans hw)
  have hcomm := (commute_matrixDifferentials_iff l f v y).mpr ((hC R v.toMul.val).mp hmem)
  have h' := (commute_matrixDifferentials_iff l f y v).mp hcomm.symm
  exact characterValue_eq_one_of_nonzero_fixedWeight G T χ v hv hne R t.toMul.val
    ((matrixCommute_iff_dualPointCommute l f hf v R y.toMul.val).mp h')

private theorem rootConditions_of_toralCentralizer
    (rootSubgroups : Specs.RootGroups.RootSubgroups.{u})
    (G : AffineAlgebraicGroup k) (hG : IsReductive G)
    {L : GroupScheme k} {I : Type u} [Fintype I] [DecidableEq I]
    (l : (groupPointsFunctor k).obj L ≅ StandardGroups.generalLinearPoints k I)
    (f : G.val ⟶ L) (hf : IsClosedImmersion f.hom.hom.left)
    (C : ClosedSubgroup G.val) (H : ClosedSubgroup C.group) (hH : IsReducedIdentityComponent H)
    (T : ClosedSubgroup G.val) (hT : IsSplitTorus T.group)
    (hmax : Specs.RankOneFlag.IsGeometricallyMaximal T) (t : Lie k T.group)
    (hC : IsMatrixCentralizer l f
      (InfinitesimalCommutator.matrixDifferential f l (mapPointKernel T.inclusion t)) C) :
    let B := subgroupOfSubgroup C H
    (∀ χ ∈ subgroupRoots T B, χ⁻¹ ∈ subgroupRoots T B) ∧
      ∀ χ ∈ subgroupRoots T B, ∀ U : ClosedSubgroup G.val,
        IsRootSubgroup T U χ → IsSubgroupOf U B := by
  dsimp only
  have hroots := (rootSubgroups G hG T hT hmax).2
  have contains (χ : Character T.group) (hχ : χ ∈ absoluteRoots T)
      (he : characterValue χ (CommAlgCat.of k (DualNumber k)) t.toMul.val = 1) :
      ∃ U : ClosedSubgroup G.val, IsSubgroupOf U (subgroupOfSubgroup C H) ∧
        CocharacterDynamics.lieImage U = adjointWeightVectors T χ ∧
        ∀ V : ClosedSubgroup G.val, IsRootSubgroup T V χ → IsSubgroupOf V U := by
    obtain ⟨_, _, U, hu, hUi, hUrange, ⟨A, x, hx⟩, huniq⟩ := hroots χ hχ
    exact ⟨U, rootSubgroup_le_component_of_character G l f hf C H hH T t hC χ he U hu x hx,
      hUrange, fun V hV => (huniq V hV).2⟩
  have ab (χ : Character T.group) (hχ : χ ∈ subgroupRoots T (subgroupOfSubgroup C H)) :
      χ ∈ absoluteRoots T := by
    obtain ⟨h, v, hv, _, hn⟩ := hχ
    exact ⟨h, v, hv, hn⟩
  constructor
  · intro χ hχ
    have hα := ab χ hχ
    have hβ := (((hroots χ hα).2.1 χ⁻¹).mpr (Or.inr rfl)).1
    have he := centralizerRootCharacters G l f hf C H T t hC χ hχ
    obtain ⟨U, hU, hUL, _⟩ := contains χ⁻¹ hβ (characterValue_inv_eq_one χ _ _ he)
    obtain ⟨hn, v, hv, hv0⟩ := hβ
    have hLie : v ∈ CocharacterDynamics.lieImage U := hUL.symm ▸ hv
    obtain ⟨z, hz⟩ := hLie
    obtain ⟨j, hj⟩ := hU
    refine ⟨hn, v, hv, ⟨mapPointKernel j z, ?_⟩, hv0⟩
    exact ((lieFunctoriality k).2.2 U.group H.group G.val j
      (subgroupOfSubgroup C H).inclusion z).symm.trans
        ((congrArg (fun a => mapPointKernel a z) hj).trans hz)
  · intro χ hχ V hV
    obtain ⟨U, hU, _, hu⟩ := contains χ (ab χ hχ)
      (centralizerRootCharacters G l f hf C H T t hC χ hχ)
    exact subgroupOf_trans (hu V hV) hU

set_option maxHeartbeats 2500000 in
/-- Reductivity of the smooth matrix centralizer component, conditionally on
the same frozen root-data premises as the symmetric-root criterion. -/
theorem semisimpleLieCentralizerComponentReductive_conditional
    (centralizer : Specs.RankOneFlag.CentralizerAndPositiveCocharacter.{u})
    (projective : Specs.RankOneFlag.ProjectiveLineAutomorphisms.{u})
    (flag : Specs.RankOneFlag.RankOneFlagGeometry.{u})
    (rankOne : Specs.RootGroups.RankOneRootGroups.{u})
    (dimension : Specs.RootGroups.RootDimension.{u})
    (rootGroups : Specs.RootGroups.RootSubgroups.{u}) :
    SemisimpleLieCentralizerComponentReductive.{u} := by
  intro k _ G hG I _ _ L l f hf y Y hy
  obtain ⟨C, hC, hsC, H, hH, hoH, hsH, hcH⟩ := smoothCentralizerComponent G hG.1 L l f hf y hy
  refine ⟨C, hC, hsC, H, hH, hoH, ?_⟩
  let B := closedSubgroupAlgebraicGroup (G := closedSubgroupAlgebraicGroup C) H
  apply reductive_of_geometricGroupReductive B hsH hcH
  let K := AlgebraicClosure k
  let GK := GeometricGroup G
  let F := groupBaseChange k K
  let CK : ClosedSubgroup GK.val :=
    baseChangedSubgroup K C (baseChangeClosedSubgroup k K C.inclusion C.isClosedImmersion)
  let HK : ClosedSubgroup CK.group :=
    baseChangedSubgroup K H (baseChangeClosedSubgroup k K H.inclusion H.isClosedImmersion)
  let BK := closedSubgroupAlgebraicGroup (G := closedSubgroupAlgebraicGroup CK) HK
  let D := subgroupOfSubgroup CK HK
  letI : IsAffine L.val.X.left := L.property
  let LK : AffineGroupCategory K := ⟨F.obj L.val, isAffine_baseChange K L.val⟩
  let lK := matrixPointsOver K l
  let fK := F.map f
  have hfK : IsClosedImmersion fK.hom.hom.left := baseChangeClosedSubgroup k K f hf
  have hGK : IsReductive GK := geometricGroupReductive G hG
  have hoK : IsOpenImmersion HK.inclusion.hom.hom.left :=
    MorphismProperty.of_isPullback (baseChangeMapIsPullback K H.inclusion.hom.hom).flip hoH
  have hsK : Smooth HK.group.X.hom := MorphismProperty.pullback_snd _ _ hsH
  have hcK : GeometricallyConnected HK.group.X.hom := MorphismProperty.pullback_snd _ _ hcH
  letI : GeometricallyConnected BK.val.X.hom := hcK
  have hconn : ConnectedSpace BK.val.X.left :=
    GeometricallyConnected.connectedSpace_of_subsingleton BK.val.X.hom
  have hHK : IsReducedIdentityComponent HK :=
    reducedIdentityComponent_of_open_closed HK hoK hsK hconn
  let s := identityLieStructure G
  let sK := identityLieStructure GK
  obtain ⟨e, he⟩ := (identityLieBracketBaseChange k K G).2 s sK
  let yK : Lie K GK.val := by
    letI := s.lieRing
    letI := s.lieAlgebra
    letI := sK.lieRing
    letI := sK.lieAlgebra
    exact e ((1 : K) ⊗ₜ[k] y)
  have hY : InfinitesimalCommutator.matrixDifferential fK lK yK = Y.map (algebraMap k K) :=
    matrixDifferential_baseChange K l f y yK (he y)
  have hCK : IsMatrixCentralizer lK fK (InfinitesimalCommutator.matrixDifferential fK lK yK) CK :=
    hY.symm ▸ baseChangeMatrixCentralizer K l f Y C hC
  obtain ⟨v, hv⟩ := matrixCentralizer_contains_its_direction lK fK yK CK hCK
  obtain ⟨z, hz⟩ := tangent_surjective_of_open HK hoK v
  have hyK : mapPointKernel D.inclusion z = yK := by
    have h := (lieFunctoriality K).2.2 HK.group CK.group GK.val HK.inclusion CK.inclusion z
    exact h.trans ((congrArg (mapPointKernel CK.inclusion) hz).trans hv)
  let fB := D.inclusion ≫ fK
  letI := D.isClosedImmersion
  letI := hfK
  have hfB : IsClosedImmersion fB.hom.hom.left := IsClosedImmersion.comp _ _
  have hBdiff : InfinitesimalCommutator.matrixDifferential fB lK z =
      InfinitesimalCommutator.matrixDifferential fK lK yK :=
    (matrixDifferential_comp D.inclusion fK lK z).trans
      (congrArg (InfinitesimalCommutator.matrixDifferential fK lK) hyK)
  have hBsem : Module.End.IsSemisimple (Matrix.toLinAlgEquiv'
      (InfinitesimalCommutator.matrixDifferential fB lK z)) := by
    rw [hBdiff, hY]
    exact hy
  have hBcen (R : TestAlgebra K) (b : GroupPoints BK.val R) :
      Commute (lK.hom.app R (onPoints fB R b)).val
        ((InfinitesimalCommutator.matrixDifferential fB lK z).map (algebraMap K R)) := by
    rw [hBdiff]
    exact (hCK R (onPoints CK.inclusion R (onPoints HK.inclusion R b))).mp
      ⟨onPoints HK.inclusion R b, rfl⟩
  obtain ⟨T, hT⟩ := maximalTorus_exists BK hsK hconn
  obtain ⟨t, ht⟩ := semisimpleCentralLie_in_maximalTorus
    BK hsK hconn T hT LK lK fB hfB z hBsem hBcen
  let S := subgroupOfSubgroup D T
  have htK : mapPointKernel S.inclusion t = yK := by
    have h := (lieFunctoriality K).2.2 T.group BK.val GK.val T.inclusion D.inclusion t
    exact h.trans ((congrArg (mapPointKernel D.inclusion) ht).trans hyK)
  have hcTor : IsMatrixCentralizer lK fK
      (InfinitesimalCommutator.matrixDifferential fK lK (mapPointKernel S.inclusion t)) CK :=
    htK.symm ▸ hCK
  have hmax : IsMaximalTorus S :=
    torusOfCentralizer_maximal GK lK fK hfK CK HK hHK T hT t hcTor
  have hsplit : IsSplitTorus S.group :=
    split_of_torus ((isTorus_iff_coordinates (closedSubgroupAlgebraicGroup S)).mp hmax.1)
  obtain ⟨hrSymm, hrInc⟩ := rootConditions_of_toralCentralizer rootGroups GK hGK lK fK hfK
    CK HK hHK S hsplit (maximalTorus_over_closure GK S hmax) t hcTor
  exact reductiveOfSymmetricRoots_conditional centralizer projective flag rankOne dimension
    rootGroups GK hGK D hsK hcK S hmax ⟨T.inclusion, rfl⟩ hrSymm hrInc

end

end LinearAlgebraicGroups.Relative.ReductiveLieCentralizers

universe v8_closure_bb61a5191d5765a0_u0
theorem _root_.«LinearAlgebraicGroups».«Relative».«ReductiveLieCentralizers».«reductiveOfSymmetricRoots» : _root_.«LinearAlgebraicGroups».«Specs».«Relative».«ReductiveLieCentralizers».«ReductiveOfSymmetricRoots».{v8_closure_bb61a5191d5765a0_u0} :=
  @_root_.«LinearAlgebraicGroups».«Relative».«ReductiveLieCentralizers».«reductiveOfSymmetricRoots_conditional».{v8_closure_bb61a5191d5765a0_u0} (@_root_.«LinearAlgebraicGroups».«RankOneFlag».«centralizerAndPositiveCocharacter».{v8_closure_bb61a5191d5765a0_u0}) (@_root_.«LinearAlgebraicGroups».«RankOneFlag».«projectiveLineAutomorphisms».{v8_closure_bb61a5191d5765a0_u0}) (@_root_.«LinearAlgebraicGroups».«RankOneFlag».«rankOneFlagGeometry».{v8_closure_bb61a5191d5765a0_u0}) (@_root_.«LinearAlgebraicGroups».«RootData».«RootGroups».«rankOneRootGroups».{v8_closure_bb61a5191d5765a0_u0}) (@_root_.«LinearAlgebraicGroups».«RootData».«RootGroups».«rootDimension».{v8_closure_bb61a5191d5765a0_u0}) (@_root_.«LinearAlgebraicGroups».«RootData».«RootGroups».«rootSubgroups».{v8_closure_bb61a5191d5765a0_u0})
theorem _root_.«LinearAlgebraicGroups».«Relative».«ReductiveLieCentralizers».«semisimpleLieCentralizerComponentReductive» : _root_.«LinearAlgebraicGroups».«Specs».«Relative».«ReductiveLieCentralizers».«SemisimpleLieCentralizerComponentReductive».{v8_closure_bb61a5191d5765a0_u0} :=
  @_root_.«LinearAlgebraicGroups».«Relative».«ReductiveLieCentralizers».«semisimpleLieCentralizerComponentReductive_conditional».{v8_closure_bb61a5191d5765a0_u0} (@_root_.«LinearAlgebraicGroups».«RankOneFlag».«centralizerAndPositiveCocharacter».{v8_closure_bb61a5191d5765a0_u0}) (@_root_.«LinearAlgebraicGroups».«RankOneFlag».«projectiveLineAutomorphisms».{v8_closure_bb61a5191d5765a0_u0}) (@_root_.«LinearAlgebraicGroups».«RankOneFlag».«rankOneFlagGeometry».{v8_closure_bb61a5191d5765a0_u0}) (@_root_.«LinearAlgebraicGroups».«RootData».«RootGroups».«rankOneRootGroups».{v8_closure_bb61a5191d5765a0_u0}) (@_root_.«LinearAlgebraicGroups».«RootData».«RootGroups».«rootDimension».{v8_closure_bb61a5191d5765a0_u0}) (@_root_.«LinearAlgebraicGroups».«RootData».«RootGroups».«rootSubgroups».{v8_closure_bb61a5191d5765a0_u0})
