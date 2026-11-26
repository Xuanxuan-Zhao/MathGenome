import Specs.LinearAlgebraicGroups.Relative.RationalCocharacter
import LinearAlgebraicGroups.Flag.StandardParabolics
import LinearAlgebraicGroups.Reductive.MaximalToriExist
import LinearAlgebraicGroups.Reductive.SubtorusCentralizer
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Pasting
import Batteries.Tactic.OpenPrivate
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Group.Int
import Mathlib.Algebra.BigOperators.GroupWithZero.Action

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open CategoryTheory.SemiCartesianMonoidalCategory (toUnit)
open scoped CategoryTheory.MonoidalCategory CategoryTheory.MonObj CategoryTheory.Obj BigOperators

universe u

namespace LinearAlgebraicGroups.Relative.RationalCocharacter

open _root_.LinearAlgebraicGroups.Specs

open Specs.BorelProper (IsParabolic)
open Specs.BorelsAndChambers (subgroupRoots)
open Specs.CharacterPairing (absoluteRoots pairing)
open Specs.CharacterDescent (Cocharacter)
open Specs.GeometricBorelConjugacy (IsBorel IsKBorel subgroupOfSubgroup)
open Specs.GeometricRadicals (GeometricGroup IsReductive IsSplitTorus IsTorus IsMaximalTorus)
open Specs.RankOneFlag (IsGeometricallyMaximal SameSubgroup)
open Specs.SchemeDerivedGroup (IsSubgroupOf)
open Specs.StandardParabolicLevi (IsContractingRadical)
open Specs.StandardParabolics
open Specs.Unipotent (closedSubgroupAlgebraicGroup)
open LinearAlgebraicGroups.CocharacterDynamics

open private isKBorel_iff_of_isAlgClosed maximal_torus_in_borel
  geometricMaximal_of_maximal split_of_maximal from LinearAlgebraicGroups.RootData.BorelNormalizer
open private reductive_geometricGroup subgroupOf_limit_of_rootSigns
  connected_baseChangedGroup smooth_baseChangedGroup
  cocharacter_weight_coordinates connected_of_geometricallyConnected torus_subgroupOf_centralizer
  lieImage_eq_of_same
  from LinearAlgebraicGroups.RootData.BorelsAndChambers
open private subgroupOf_trans from LinearAlgebraicGroups.Reductive.GeometricBorelConjugacy
open private subgroupIso_of_same extendSubgroup extend_subgroupOf subgroupOf_of_extend
  cocharacter_ext_units limits_subgroups_extend same_subgroup_trans same_subgroup_symm
  from LinearAlgebraicGroups.RootData.RankOneFlag
open private restrictSubgroup compose_restrict local_maximal_of_ambient
  conjugates_in_ambient conjugates_maximal conjugates_preserves_borel
  conjugationIso conjugate comp_conjugate
  from LinearAlgebraicGroups.Reductive.MaximalToriConjugate
open private transportSubgroup borel_transport from LinearAlgebraicGroups.Reductive.BorelProper
open private canonicalZero_eq from LinearAlgebraicGroups.RootData.CharacterPairing
open private fieldSpecMap_surjective from LinearAlgebraicGroups.Affine.Stabilizers

noncomputable section

set_option maxHeartbeats 1200000
set_option linter.style.haveILetI false
set_option backward.isDefEq.respectTransparency false

variable {k : Type u} [Field k]

/-- The sum of a finite orbit is fixed and preserves any common weak sign. -/
private theorem invariantIntegralSum {Γ Y : Type*} [Group Γ] [Fintype Γ] [AddCommGroup Y]
    [DistribMulAction Γ Y] (y : Y) :
    ∃ z : Y, (∀ g : Γ, g • z = z) ∧
      ∀ w : Y →+ ℤ, (∀ g : Γ, 0 ≤ w (g • y) ↔ 0 ≤ w y) → (0 ≤ w z ↔ 0 ≤ w y) := by
  classical
  refine ⟨∑ g : Γ, g • y, ?_, ?_⟩
  · intro a
    rw [Finset.smul_sum]
    simp only [← mul_smul]
    exact Equiv.sum_comp (Equiv.mulLeft a) (fun g : Γ ↦ g • y)
  · intro w h
    rw [map_sum]
    constructor
    · intro hs
      by_contra! hn
      have hneg : ∑ g : Γ, w (g • y) < 0 :=
        Finset.sum_neg (fun g _ ↦ lt_of_not_ge fun hg ↦ (not_le.mpr hn) ((h g).mp hg))
          Finset.univ_nonempty
      exact (not_le.mpr hneg) hs
    · intro hp
      exact Finset.sum_nonneg fun g _ ↦ (h g).mpr hp

private theorem splitParabolic (classify : StandardParabolicClassification.{u})
    (G : AffineAlgebraicGroup k) (P T B : ClosedSubgroup G.val)
    (hP : IsParabolic G P) (hT : IsSplitTorus T.group) (hTm : IsGeometricallyMaximal T)
    (hB : IsKBorel B) (hTB : IsSubgroupOf T B) (hBP : IsSubgroupOf B P) :
    ∃ (c : Cocharacter T.group) (D : LimitDecomposition (c ≫ T.inclusion)),
      SameSubgroup P D.parabolic := by
  obtain ⟨hcomm, rest⟩ := classify G hP.1 T B hT hTm hB hTB
  letI := hcomm
  obtain ⟨_, _, _, _, _, _, _, _, _, family, _, hf⟩ := rest
  obtain ⟨hIndex, hSame⟩ := hf P hP hBP
  obtain ⟨I, hi, _⟩ := hIndex
  let M := family I
  exact ⟨M.cocharacter, M.limitGroups, (hSame I).mp hi⟩

section SplitCocharacters

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 380000

open Opposite
open scoped MonoidAlgebra TensorProduct
open Specs.DiagonalizableGroups (groupAlgebra groupAlgebraMap IntegerCharacters)
open Specs.CharacterDescent (StandardLattice)
open private extendedGroupIso extendedSpecIso_natural specGroupMap_comp
  from LinearAlgebraicGroups.Affine.ClosedSubgroups
open private splitGroupHomEquiv from LinearAlgebraicGroups.Multiplicative.CharacterDescent

private noncomputable def splitCoordinateComparison
    (K : Type u) [Field K] [Algebra k K] (M : Type u) [CommGroup M] :
    extendedHopf K (groupAlgebra k M) ≅ groupAlgebra K M :=
  CommHopfAlgCat.isoMk
    (LinearAlgebraicGroups.CharacterDescent.groupAlgebraBaseChange k K M)

private theorem splitCoordinateComparison_naturality
    (K : Type u) [Field K] [Algebra k K] {M N : Type u} [CommGroup M] [CommGroup N]
    (f : M →* N) :
    extendedHopfMap K (groupAlgebraMap k f) ≫ (splitCoordinateComparison K N).hom =
      (splitCoordinateComparison K M).hom ≫ groupAlgebraMap K f := by
  apply CommHopfAlgCat.hom_ext
  apply BialgHom.coe_toAlgHom_injective
  apply Algebra.TensorProduct.ext_ring
  apply MonoidAlgebra.algHom_ext
  · intro m
    let b := LinearAlgebraicGroups.CharacterDescent.groupAlgebraBaseChange
    have h (A : Type u) [CommGroup A] (x : A) :
        b k K A ((1 : K) ⊗ₜ[k] MonoidAlgebra.single x (1 : k)) = MonoidAlgebra.single x 1 :=
      ((b k K A).toEquiv.eq_symm_apply).mp
        (MonoidAlgebra.scalarTensorEquiv_symm_single (R := k) (A := K) x 1).symm
    change b k K N (1 ⊗ₜ[k] MonoidAlgebra.mapDomainBialgHom k f (MonoidAlgebra.single m 1)) =
      MonoidAlgebra.mapDomainBialgHom K f (b k K M (1 ⊗ₜ[k] MonoidAlgebra.single m 1))
    rw [h, MonoidAlgebra.mapDomainBialgHom_single, MonoidAlgebra.mapDomainBialgHom_single, h]
  · ext

private noncomputable def splitSchemeComparison
    (K : Type u) [Field K] [Algebra k K] (M : Type u) [CommGroup M] :
    specGroup (groupAlgebra K M) ≅ (groupBaseChange k K).obj (specGroup (groupAlgebra k M)) :=
  (hopfSpec (CommRingCat.of K)).mapIso (splitCoordinateComparison K M).op ≪≫
    extendedGroupIso K (groupAlgebra k M)

private theorem splitSchemeComparison_naturality
    (K : Type u) [Field K] [Algebra k K] {M N : Type u} [CommGroup M] [CommGroup N]
    (f : M →* N) :
    specGroupMap (groupAlgebraMap K f) ≫ (splitSchemeComparison K M).hom =
      (splitSchemeComparison K N).hom ≫ (groupBaseChange k K).map (specGroupMap (groupAlgebraMap k f)) := by
  let a := groupAlgebraMap k f
  let b := groupAlgebraMap K f
  let i := splitCoordinateComparison (k := k) K M
  let j := splitCoordinateComparison (k := k) K N
  have he : extendedHopfMap K a ≫ j.hom = i.hom ≫ b :=
    splitCoordinateComparison_naturality (k := k) K f
  have he' : specGroupMap (extendedHopfMap K a) ≫ (extendedGroupIso K (groupAlgebra k M)).hom =
      (extendedGroupIso K (groupAlgebra k N)).hom ≫ (groupBaseChange k K).map (specGroupMap a) :=
    Grp.hom_ext _ _ (extendedSpecIso_natural K a)
  have he'' := congrArg (fun x : extendedHopf K (groupAlgebra k M) ⟶ groupAlgebra K N =>
    specGroupMap x) he
  rw [specGroupMap_comp, specGroupMap_comp] at he''
  change specGroupMap b ≫ (specGroupMap i.hom ≫ (extendedGroupIso K (groupAlgebra k M)).hom) =
    (specGroupMap j.hom ≫ (extendedGroupIso K (groupAlgebra k N)).hom) ≫
      (groupBaseChange k K).map (specGroupMap a)
  rw [← Category.assoc, ← he'', Category.assoc, he', Category.assoc]

/-- Cocharacters of a split diagonalizable group lift along field extension. -/
private theorem liftSplitCocharacter
    (K : Type u) [Field K] [Algebra k K] {T : GroupScheme k}
    {M : Type u} [CommGroup M] (q : specGroup (groupAlgebra k M) ≅ T)
    (e : specGroup (groupAlgebra K IntegerCharacters) ≅
      (groupBaseChange k K).obj (specGroup (groupAlgebra k IntegerCharacters)))
    (c : Cocharacter ((groupBaseChange k K).obj T)) :
    ∃ d : Cocharacter T, e.hom ≫ (groupBaseChange k K).map d = c := by
  let F := groupBaseChange k K
  let i := splitSchemeComparison (k := k) K IntegerCharacters
  let j := splitSchemeComparison (k := k) K M
  let c' := i.hom ≫ e.inv ≫ c ≫ F.map q.inv ≫ j.inv
  obtain ⟨f, hf⟩ := (splitGroupHomEquiv (k := K) M IntegerCharacters).surjective c'
  change specGroupMap (groupAlgebraMap K f) = c' at hf
  refine ⟨specGroupMap (groupAlgebraMap k f) ≫ q.hom, ?_⟩
  have hw : i.hom ≫ F.map (specGroupMap (groupAlgebraMap k f) ≫ q.hom) =
      i.hom ≫ e.inv ≫ c := by
    rw [Functor.map_comp, ← Category.assoc i.hom,
      ← splitSchemeComparison_naturality K f, hf]
    change (i.hom ≫ e.inv ≫ c ≫ F.map q.inv ≫ j.inv) ≫ j.hom ≫ F.map q.hom = _
    simp only [Category.assoc, Iso.inv_hom_id_assoc, ← Functor.map_comp,
      q.inv_hom_id]
    rw [F.map_id, Category.comp_id]
  apply (Iso.cancel_iso_inv_left e _ _).mp
  rw [Iso.inv_hom_id_assoc]
  exact (Iso.cancel_iso_hom_left i _ _).mp hw

end SplitCocharacters

/-- Membership of a root in the Lie algebra of a limit parabolic is equivalent
to nonnegative pairing with its defining cocharacter. -/
private theorem limitParabolic_root_iff
    (G : AffineAlgebraicGroup k) (T : ClosedSubgroup G.val) (c : Cocharacter T.group)
    (D : LimitDecomposition (c ≫ T.inclusion)) (α : absoluteRoots T) :
    α ∈ subgroupRoots T D.parabolic ↔ 0 ≤ pairing T.group α.val c := by
  let s := identityLieStructure G
  letI := s.lieRing
  letI := s.lieAlgebra
  obtain ⟨W, hW, _, _⟩ := lieWeights G _ D s
  constructor
  · intro h
    by_contra! hn
    obtain ⟨_, v, hv, hv0⟩ := α.property
    have hp := h hv
    rw [hW] at hp
    apply hv0
    have hzero (j : ULift.{u} (Fin W.dimension)) : W.basis.equivFun v j = 0 := by
      by_cases hj : W.weight j = pairing T.group α.val c
      · exact hp j (hj.symm ▸ hn)
      · exact cocharacter_weight_coordinates T c s W hv j hj
    exact (W.basis.equivFun.injective
      ((funext hzero).trans W.basis.equivFun.map_zero.symm)).trans (canonicalZero_eq s).symm
  · intro h v hv
    rw [hW]
    intro j hj
    exact cocharacter_weight_coordinates T c s W hv j (by omega)

/-- A split-torus cocharacter may be replaced by another with the same
nonnegative absolute roots. -/
private theorem sameLimitParabolic_of_nonnegativeRoots
    (G : AffineAlgebraicGroup k) (hG : IsReductive G) (T : ClosedSubgroup G.val)
    (hT : IsSplitTorus T.group) (hTm : IsGeometricallyMaximal T)
    (c d : Cocharacter T.group) (C : LimitDecomposition (c ≫ T.inclusion))
    (D : LimitDecomposition (d ≫ T.inclusion))
    (h : ∀ α : absoluteRoots T, 0 ≤ pairing T.group α.val c ↔ 0 ≤ pairing T.group α.val d) :
    SameSubgroup C.parabolic D.parabolic := by
  letI := hG.1
  letI : ConnectedSpace G.val.X.left := connected_of_geometricallyConnected hG.2.1
  have included (a b : Cocharacter T.group) (A : LimitDecomposition (a ≫ T.inclusion))
      (B : LimitDecomposition (b ≫ T.inclusion))
      (hab : ∀ α : absoluteRoots T, 0 ≤ pairing T.group α.val a → 0 ≤ pairing T.group α.val b) :
      IsSubgroupOf A.parabolic B.parabolic := by
    apply subgroupOf_limit_of_rootSigns G hG T A.parabolic hT hTm (limitSubgroupsSmooth G _ A).1
      (connected_of_geometricallyConnected (geometricallyConnectedLimitSubgroups G _ A).1)
      (subgroupOf_trans (torus_subgroupOf_centralizer hT a A) ⟨A.sectionMap, A.section_in_G⟩)
      b B
    intro α hα
    exact hab α ((limitParabolic_root_iff G T a A α).mp hα)
  exact ⟨included c d C D (fun α ↦ (h α).mp), included d c D C (fun α ↦ (h α).mpr)⟩

private theorem geometricParabolicConnected (classify : StandardParabolicClassification.{u})
    [IsAlgClosed k] (G : AffineAlgebraicGroup k) (P B : ClosedSubgroup G.val)
    (hG : IsReductive G) (hP : Smooth P.group.X.hom) (hB : IsBorel B)
    (hBP : IsSubgroupOf B P) : ConnectedSpace P.group.X.left := by
  have hBk := (isKBorel_iff_of_isAlgClosed G B).mpr hB
  have hp : IsParabolic G P :=
    ⟨hG, hP, (extendSubgroup (AlgebraicClosure k) P).isClosedImmersion,
      extendSubgroup (AlgebraicClosure k) B, hBk.choose_spec, extend_subgroupOf hBP⟩
  obtain ⟨S, _, hS⟩ := maximal_torus_in_borel G hG B hB
  let T := subgroupOfSubgroup B S
  have hTs : IsSplitTorus T.group := split_of_maximal (A := G) hS
  have hTm := geometricMaximal_of_maximal G T hS
  obtain ⟨c, D, hEq⟩ :=
    splitParabolic classify G P T B hp hTs hTm hBk ⟨S.inclusion, rfl⟩ hBP
  letI := hG.1
  letI := hG.2.1
  letI : ConnectedSpace G.val.X.left :=
    GeometricallyConnected.connectedSpace_of_subsingleton G.val.X.hom
  have hconn : ConnectedSpace D.parabolic.group.X.left :=
    connected_of_geometricallyConnected (geometricallyConnectedLimitSubgroups G _ D).1
  obtain ⟨e, _⟩ := subgroupIso_of_same hEq
  let f := ((Grp.forget (SchemeOver k)) ⋙ Over.forget _).mapIso e
  exact f.hom.homeomorph.connectedSpace_iff.mpr hconn

/-- Over an algebraically closed field the Borel used in the split classification
can be chosen inside the parabolic and through its prescribed maximal torus. -/
private theorem geometricBorelThroughTorus (classify : StandardParabolicClassification.{u})
    [IsAlgClosed k] (G : AffineAlgebraicGroup k) (P B : ClosedSubgroup G.val)
    (hG : IsReductive G) (hP : Smooth P.group.X.hom) (hB : IsBorel B)
    (hBP : IsSubgroupOf B P) (T : ClosedSubgroup P.group) (hT : IsMaximalTorus T) :
    IsMaximalTorus (subgroupOfSubgroup P T) ∧
      ∃ C : ClosedSubgroup G.val, IsBorel C ∧
        IsSubgroupOf (subgroupOfSubgroup P T) C ∧ IsSubgroupOf C P := by
  obtain ⟨S, _, hS⟩ := maximal_torus_in_borel G hG B hB
  let Sg := subgroupOfSubgroup B S
  have hPc := geometricParabolicConnected classify G P B hG hP hB hBP
  obtain ⟨b, hb⟩ := hBP
  let j := S.inclusion ≫ b
  have hj : j ≫ P.inclusion = Sg.inclusion := by
    change (S.inclusion ≫ b) ≫ P.inclusion = S.inclusion ≫ B.inclusion
    rw [Category.assoc, hb]
  let Sp := restrictSubgroup Sg P j hj
  have hSpG : IsMaximalTorus (subgroupOfSubgroup P Sp) :=
    (compose_restrict Sg P j hj).symm ▸ hS
  obtain ⟨g, hg⟩ := MaximalToriConjugate.maximalToriConjugate
    (closedSubgroupAlgebraicGroup P) hP hPc Sp T (local_maximal_of_ambient P Sp hSpG) hT
  let x := g ≫ P.inclusion.hom.hom
  let e := conjugationIso x
  let C := transportSubgroup B e
  have hx := conjugates_in_ambient P hg
  have hTmax := conjugates_maximal hx hSpG
  obtain ⟨i, hi⟩ := hx
  obtain ⟨p, hp⟩ := conjugates_preserves_borel P g
  refine ⟨hTmax, C, borel_transport hB e, ?_, ?_⟩
  · refine ⟨i.inv ≫ S.inclusion, ?_⟩
    have hi' : i.hom ≫ (subgroupOfSubgroup P T).inclusion =
        (subgroupOfSubgroup P Sp).inclusion ≫ e.hom := by
      apply Grp.hom_ext
      change _ = (subgroupOfSubgroup P Sp).inclusion.hom.hom ≫ conjugate x (𝟙 G.val.X)
      rw [comp_conjugate, Category.comp_id]
      exact hi
    change (i.inv ≫ S.inclusion) ≫ (B.inclusion ≫ e.hom) = _
    rw [Category.assoc, ← Category.assoc S.inclusion,
      ← show (subgroupOfSubgroup P Sp).inclusion = S.inclusion ≫ B.inclusion from hj,
      ← hi', i.inv_hom_id_assoc]
  · refine ⟨b ≫ p.hom, ?_⟩
    have hp' : p.hom ≫ P.inclusion = P.inclusion ≫ e.hom := by
      apply Grp.hom_ext
      change _ = P.inclusion.hom.hom ≫ conjugate x (𝟙 G.val.X)
      rw [comp_conjugate, Category.comp_id]
      exact hp
    change (b ≫ p.hom) ≫ P.inclusion = B.inclusion ≫ e.hom
    rw [Category.assoc, hp', ← Category.assoc, hb]

private theorem parabolicConnected (classify : StandardParabolicClassification.{u})
    (G : AffineAlgebraicGroup k) (P : ClosedSubgroup G.val) (hP : IsParabolic G P) :
    ConnectedSpace P.group.X.left := by
  let K := AlgebraicClosure k
  let Gbar := GeometricGroup G
  let Pbar := extendSubgroup K P
  obtain ⟨_, B, hB, hBP⟩ := hP.2.2
  have hPs : Smooth Pbar.group.X.hom := MorphismProperty.pullback_snd _ _ hP.2.1
  letI : ConnectedSpace ↥(Limits.pullback P.group.X.hom (fieldSpecMap k K) : Scheme.{u}) :=
    geometricParabolicConnected classify Gbar Pbar B (reductive_geometricGroup G hP.1) hPs hB hBP
  letI : Surjective (fieldSpecMap k K) := fieldSpecMap_surjective K
  let f := Limits.pullback.fst P.group.X.hom (fieldSpecMap k K)
  have hf : Surjective f := inferInstanceAs (Surjective (Limits.pullback.fst _ _))
  exact hf.1.connectedSpace f.continuous

open private exists_maximal_torus_over inclusion_mono
  from LinearAlgebraicGroups.Reductive.MaximalToriConjugate
open private torus_commutative torus_in_centralizer
  from LinearAlgebraicGroups.Reductive.TorusFreeUnipotent
open private conjugate_comp from LinearAlgebraicGroups.Reductive.MaximalToriConjugate
open private torus_after_algClosed_extension from LinearAlgebraicGroups.Reductive.MaximalToriExist
open private factor_group_through_subgroup
  from LinearAlgebraicGroups.Reductive.GeometricBorelConjugacy
open private centralizes_iff mono_over from LinearAlgebraicGroups.Affine.Stabilizers

/-- Maximality among ground-field tori implies geometric maximality. A
geometrically maximal torus in the centralizer of the given torus must
contain it, by conjugacy and centrality. -/
private theorem geometricMaximal_of_rationalMaximal
    (G : AffineAlgebraicGroup k) (hGs : Smooth G.val.X.hom)
    (hGc : ConnectedSpace G.val.X.left) (T : ClosedSubgroup G.val) (hT : IsMaximalTorus T) :
    IsGeometricallyMaximal T := by
  letI := hGs
  letI := hGc
  obtain ⟨C, hC, hCs, hCc⟩ := connectedTorusCentralizer G T hT.1
  let A := closedSubgroupAlgebraicGroup (G := G) C
  obtain ⟨j, hjc, hj, _⟩ := torus_in_centralizer (G := G)
    (torus_commutative (closedSubgroupAlgebraicGroup (G := G) T) hT.1) hC
  let N : ClosedSubgroup C.group := ⟨T.group, j, hjc⟩
  obtain ⟨S, hS, _, hSm⟩ := MaximalToriExist.geometricallyMaximalTorusExists A hCs
    (connected_of_geometricallyConnected hCc)
  let K := AlgebraicClosure k
  let Gbar := GeometricGroup G
  let Abar := GeometricGroup A
  let Cbar := extendSubgroup K C
  let Tbar := extendSubgroup K T
  let Nbar := extendSubgroup K N
  let Sbar := extendSubgroup K S
  have hCbar : RepresentsSubgroup Cbar (fun _ g ↦ Centralizes Tbar.inclusion g) :=
    (LinearAlgebraicGroups.centralizerSchemeBaseChange k K T.inclusion C hC).choose_spec
  have hNbar : Nbar.inclusion ≫ Cbar.inclusion = Tbar.inclusion := by
    change (groupBaseChange k K).map j ≫ (groupBaseChange k K).map C.inclusion =
      (groupBaseChange k K).map T.inclusion
    rw [← Functor.map_comp, hj]
  have hTbar : IsTorus Tbar.group :=
    torus_after_algClosed_extension K (closedSubgroupAlgebraicGroup (G := G) T) hT.1
  obtain ⟨V, hV, hNV⟩ := exists_maximal_torus_over Abar Nbar hTbar
  obtain ⟨g, e, he⟩ := MaximalToriConjugate.maximalToriConjugate Abar
    (smooth_baseChangedGroup hCs)
    (connected_baseChangedGroup (K := K) A (connected_of_geometricallyConnected hCc))
    V Sbar hV hSm
  have hconj : conjugate g Nbar.inclusion.hom.hom = Nbar.inclusion.hom.hom := by
    letI : Mono Cbar.inclusion.hom.hom := mono_over _ Cbar.isClosedImmersion
    apply (cancel_mono Cbar.inclusion.hom.hom).mp
    rw [conjugate_comp, ← show (Nbar.inclusion ≫ Cbar.inclusion).hom.hom =
      Nbar.inclusion.hom.hom ≫ Cbar.inclusion.hom.hom from rfl, hNbar]
    have hh := (hCbar _ (g ≫ Cbar.inclusion.hom.hom)).mpr ⟨g, rfl⟩
    have ht := (centralizes_iff _ _).mp hh Tbar.group.X (toUnit Tbar.group.X) (𝟙 _)
    change Commute (toUnit Tbar.group.X ≫ (g ≫ Cbar.inclusion.hom.hom))
      ((𝟙 _) ≫ Tbar.inclusion.hom.hom) at ht
    rw [Category.id_comp] at ht
    exact (mul_inv_eq_iff_eq_mul).mpr ht.eq
  obtain ⟨a, ha⟩ := hNV
  have hNSbar : IsSubgroupOf Nbar Sbar := by
    refine ⟨a ≫ e.hom, ?_⟩
    apply Grp.hom_ext
    change a.hom.hom ≫ (e.hom ≫ Sbar.inclusion).hom.hom = Nbar.inclusion.hom.hom
    change (e.hom ≫ Sbar.inclusion).hom.hom = conjugate g V.inclusion.hom.hom at he
    have ha' : a.hom.hom ≫ V.inclusion.hom.hom = Nbar.inclusion.hom.hom :=
      (Grp.forget _).congr_map ha
    rw [he, comp_conjugate, ha', hconj]
  obtain ⟨b, hb⟩ := subgroupOf_of_extend (K := K) hNSbar
  let SC := subgroupOfSubgroup C S
  have hTSC : IsSubgroupOf T SC := by
    refine ⟨b, ?_⟩
    change b ≫ S.inclusion ≫ C.inclusion = T.inclusion
    rw [← Category.assoc, hb, hj]
  obtain ⟨d, hd⟩ := hT.2 SC hS hTSC
  refine ⟨Tbar.isClosedImmersion, hTbar, ?_⟩
  intro R hR hTR
  obtain ⟨p, hp⟩ := hTR
  change p ≫ R.inclusion = Tbar.inclusion at hp
  have hRC : Centralizes Tbar.inclusion R.inclusion.hom.hom := by
    apply (centralizes_iff _ _).mpr
    intro Y r t
    letI : IsCommMonObj R.group.X := torus_commutative (closedSubgroupAlgebraicGroup (G := Gbar) R) hR
    have hh : Commute r (t ≫ p.hom.hom) := Commute.all r (t ≫ p.hom.hom)
    have hm := hh.map (IsMonHom.monoidHom R.inclusion.hom.hom Y)
    change Commute (r ≫ R.inclusion.hom.hom)
      ((t ≫ p.hom.hom) ≫ R.inclusion.hom.hom) at hm
    rw [Category.assoc, ← show (p ≫ R.inclusion).hom.hom =
      p.hom.hom ≫ R.inclusion.hom.hom from rfl, hp] at hm
    exact hm
  obtain ⟨z, hz⟩ := (hCbar _ _).mp hRC
  obtain ⟨f, hf⟩ := factor_group_through_subgroup Cbar R.inclusion z hz
  let RC := restrictSubgroup R Cbar f hf
  let F := groupBaseChange k K
  letI := inclusion_mono Cbar
  have hSR : IsSubgroupOf Sbar RC := by
    refine ⟨F.map d ≫ p, (cancel_mono Cbar.inclusion).mp ?_⟩
    change (F.map d ≫ p) ≫ f ≫ Cbar.inclusion = F.map S.inclusion ≫ F.map C.inclusion
    calc
      (F.map d ≫ p) ≫ f ≫ Cbar.inclusion = F.map d ≫ F.map T.inclusion := by
        change (F.map d ≫ p) ≫ f ≫ Cbar.inclusion = F.map d ≫ Tbar.inclusion
        rw [hf, Category.assoc, hp]
      _ = F.map S.inclusion ≫ F.map C.inclusion := by
        rw [← F.map_comp, hd]
        exact F.map_comp S.inclusion C.inclusion
  obtain ⟨l, hl⟩ := hSm.2 RC hR hSR
  change l ≫ F.map S.inclusion = f at hl
  refine ⟨l ≫ F.map d, ?_⟩
  change (l ≫ F.map d) ≫ F.map T.inclusion = R.inclusion
  calc
    (l ≫ F.map d) ≫ F.map T.inclusion = l ≫ F.map (d ≫ T.inclusion) := by
      rw [F.map_comp, Category.assoc]
    _ = (l ≫ F.map S.inclusion) ≫ F.map C.inclusion := by
      rw [hd]
      change l ≫ F.map (S.inclusion ≫ C.inclusion) = _
      rw [F.map_comp, Category.assoc]
    _ = R.inclusion := by
      rw [hl]
      exact hf

/-- The weak root signs depend only on the limit parabolic. -/
private theorem limitParabolic_signs_of_same
    (G : AffineAlgebraicGroup k) (T : ClosedSubgroup G.val)
    (c d : Cocharacter T.group) (C : LimitDecomposition (c ≫ T.inclusion))
    (D : LimitDecomposition (d ≫ T.inclusion)) (hCD : SameSubgroup C.parabolic D.parabolic)
    (α : absoluteRoots T) :
    (0 ≤ pairing T.group α.val c ↔ 0 ≤ pairing T.group α.val d) := by
  have hRoots : subgroupRoots T C.parabolic = subgroupRoots T D.parabolic := by
    unfold subgroupRoots
    rw [lieImage_eq_of_same hCD]
  rw [← limitParabolic_root_iff G T c C α, ← limitParabolic_root_iff G T d D α, hRoots]

section ScalarTower

open CategoryTheory.Limits Opposite
open scoped CategoryTheory.MonoidalCategory CategoryTheory.MonObj
open Specs.AdjointRepresentation (GroupPoints)
open Specs.DiagonalizableGroups (groupAlgebra IntegerCharacters)
open private gm_baseChange pointHom from LinearAlgebraicGroups.Reductive.CocharacterLimitSubgroups

private noncomputable abbrev multiplicativeGroup (k : Type u) [Field k] : GroupScheme k :=
  specGroup (groupAlgebra k IntegerCharacters)

private noncomputable abbrev extendPoints {K : Type u} [Field K] [Algebra k K]
    (G : GroupScheme k) (R : TestAlgebra K) :=
  baseChangePointGroupEquiv K G R

private noncomputable def multiplicativeBaseChange (k K : Type u) [Field k] [Field K] [Algebra k K] :
    multiplicativeGroup K ≅ (groupBaseChange k K).obj (multiplicativeGroup k) :=
  (gm_baseChange k K).choose

private theorem multiplicativeBaseChange_unit (K : Type u) [Field K] [Algebra k K]
    (R : TestAlgebra K) (s : Rˣ) :
    extendPoints (multiplicativeGroup k) R
      (pointHom (multiplicativeBaseChange k K).hom R (unitPoint R s)) =
        unitPoint ((restrictTestAlgebra k K).obj R) s :=
  (gm_baseChange k K).choose_spec R s

private noncomputable abbrev extendCocharacter (K : Type u) [Field K] [Algebra k K]
    {T : GroupScheme k} (c : Cocharacter T) : Cocharacter ((groupBaseChange k K).obj T) :=
  (multiplicativeBaseChange k K).hom ≫ (groupBaseChange k K).map c

variable {K L : Type u} [Field K] [Field L] [Algebra k K] [Algebra K L] [Algebra k L]
  [IsScalarTower k K L]

private theorem fieldSpecMap_tower :
    fieldSpecMap K L ≫ fieldSpecMap k K = fieldSpecMap k L := by
  rw [← Spec.map_comp]
  congr 1
  ext x
  exact (IsScalarTower.algebraMap_apply k K L x).symm

private noncomputable def baseChangeTowerComparison (X : SchemeOver k) :
    ((baseChange k K ⋙ baseChange K L).obj X).left ≅ ((baseChange k L).obj X).left :=
  pullbackLeftPullbackSndIso X.hom (fieldSpecMap k K) (fieldSpecMap K L) ≪≫
    pullback.congrHom rfl (fieldSpecMap_tower (k := k) (K := K) (L := L))

private theorem baseChangeTowerComparison_fst (X : SchemeOver k) :
    (baseChangeTowerComparison (K := K) (L := L) X).hom ≫
      pullback.fst X.hom (fieldSpecMap k L) =
      pullback.fst ((baseChange k K).obj X).hom (fieldSpecMap K L) ≫
        pullback.fst X.hom (fieldSpecMap k K) := by
  simp [baseChangeTowerComparison, pullback.congrHom, baseChange]

private theorem baseChangeTowerComparison_snd (X : SchemeOver k) :
    (baseChangeTowerComparison (K := K) (L := L) X).hom ≫ ((baseChange k L).obj X).hom =
      ((baseChange k K ⋙ baseChange K L).obj X).hom := by
  simp [baseChangeTowerComparison, pullback.congrHom, baseChange]

private noncomputable def baseChangeTowerIso :
    baseChange k K ⋙ baseChange K L ≅ baseChange k L :=
  NatIso.ofComponents (fun X ↦ Over.isoMk (baseChangeTowerComparison X)
    (baseChangeTowerComparison_snd X)) (by
    intro X Y a
    apply Over.OverMorphism.ext
    apply pullback.hom_ext
    · change (((baseChange k K ⋙ baseChange K L).map a).left ≫
          (baseChangeTowerComparison (K := K) (L := L) Y).hom) ≫ pullback.fst _ _ =
        ((baseChangeTowerComparison (K := K) (L := L) X).hom ≫
          ((baseChange k L).map a).left) ≫ pullback.fst _ _
      simp only [Category.assoc, baseChangeTowerComparison_fst, Functor.comp_map,
        Over.pullback_map_left, pullback.lift_fst_assoc, pullback.lift_fst]
      rw [← Category.assoc (baseChangeTowerComparison (K := K) (L := L) X).hom,
        baseChangeTowerComparison_fst, Category.assoc]
    · exact (Over.w _).trans (Over.w _).symm)

private noncomputable def groupBaseChangeTowerIso :
    groupBaseChange k K ⋙ groupBaseChange K L ≅ groupBaseChange k L :=
  Functor.mapGrpCompIso.symm ≪≫ Functor.mapGrpNatIso baseChangeTowerIso

private theorem groupBaseChangeTowerIso_fst (G : GroupScheme k) :
    ((groupBaseChangeTowerIso (K := K) (L := L)).app G).hom.hom.hom.left ≫
      pullback.fst G.X.hom (fieldSpecMap k L) =
      pullback.fst ((baseChange k K).obj G.X).hom (fieldSpecMap K L) ≫
        pullback.fst G.X.hom (fieldSpecMap k K) := by
  change (baseChangeTowerComparison (K := K) (L := L) G.X).hom ≫ _ = _
  exact baseChangeTowerComparison_fst G.X

private noncomputable def restrictTowerAlgebraIso (R : TestAlgebra L) :
    (restrictTestAlgebra k K).obj ((restrictTestAlgebra K L).obj R) ≅
      (restrictTestAlgebra k L).obj R := by
  let F := (restrictTestAlgebra k K).obj ((restrictTestAlgebra K L).obj R)
  let G := (restrictTestAlgebra k L).obj R
  let e : F ≃ₐ[k] G := AlgEquiv.ofRingEquiv (f := RingEquiv.refl R) (by
    intro x
    change algebraMap L R (algebraMap K L (algebraMap k K x)) =
      algebraMap L R (algebraMap k L x)
    rw [← IsScalarTower.algebraMap_apply k K L])
  exact ⟨ConcreteCategory.ofHom (C := CommAlgCat k) e.toAlgHom,
    ConcreteCategory.ofHom (C := CommAlgCat k) e.symm.toAlgHom,
    CommAlgCat.hom_ext (DFunLike.ext _ _ e.symm_apply_apply),
    CommAlgCat.hom_ext (DFunLike.ext _ _ e.apply_symm_apply)⟩

private theorem groupBaseChangeTowerIso_points (G : GroupScheme k) (R : TestAlgebra L)
    (p : GroupPoints ((groupBaseChange k K ⋙ groupBaseChange K L).obj G) R) :
    extendPoints G R (pointHom (groupBaseChangeTowerIso.app G).hom R p) =
      mapPoints (restrictTowerAlgebraIso (k := k) (K := K) R).hom
        (extendPoints G ((restrictTestAlgebra K L).obj R)
          (extendPoints ((groupBaseChange k K).obj G) R p)) := by
  apply Over.OverMorphism.ext
  change (p.left ≫ ((groupBaseChangeTowerIso (K := K) (L := L)).app G).hom.hom.hom.left) ≫
      pullback.fst G.X.hom (fieldSpecMap k L) =
    Spec.map (CommRingCat.ofHom (RingHom.id R)) ≫
      (p.left ≫ pullback.fst ((baseChange k K).obj G.X).hom (fieldSpecMap K L)) ≫
        pullback.fst G.X.hom (fieldSpecMap k K)
  rw [Category.assoc, groupBaseChangeTowerIso_fst]
  simp [Category.assoc]

private theorem multiplicativeBaseChange_tower :
    (multiplicativeBaseChange K L).hom ≫
      (groupBaseChange K L).map (multiplicativeBaseChange k K).hom ≫
      ((groupBaseChangeTowerIso (K := K) (L := L)).app (multiplicativeGroup k)).hom =
      (multiplicativeBaseChange k L).hom := by
  apply cocharacter_ext_units
  intro R s
  let M := multiplicativeGroup k
  let p := pointHom (multiplicativeBaseChange K L).hom R (unitPoint R s)
  let b := (groupBaseChange K L).map (multiplicativeBaseChange k K).hom
  apply (extendPoints M R).injective
  change extendPoints M R (pointHom (groupBaseChangeTowerIso.app M).hom R (pointHom b R p)) =
    extendPoints M R (pointHom (multiplicativeBaseChange k L).hom R (unitPoint R s))
  rw [groupBaseChangeTowerIso_points, multiplicativeBaseChange_unit]
  have hn : extendPoints ((groupBaseChange k K).obj M) R (pointHom b R p) =
      pointHom (multiplicativeBaseChange k K).hom ((restrictTestAlgebra K L).obj R)
        (extendPoints (multiplicativeGroup K) R p) :=
    baseChangePointsSchemeNaturality K L (multiplicativeBaseChange k K).hom.hom.hom R p
  rw [hn, multiplicativeBaseChange_unit, multiplicativeBaseChange_unit, mapPoints_unitPoint]
  rfl

private theorem extendCocharacter_tower {T : GroupScheme k} (c : Cocharacter T) :
    extendCocharacter L (extendCocharacter K c) ≫
      ((groupBaseChangeTowerIso (K := K) (L := L)).app T).hom =
      extendCocharacter L c := by
  let F := groupBaseChange K L
  let X := multiplicativeGroup k
  let n := groupBaseChangeTowerIso (k := k) (K := K) (L := L)
  change ((multiplicativeBaseChange K L).hom ≫
    F.map ((multiplicativeBaseChange k K).hom ≫ (groupBaseChange k K).map c)) ≫
      (n.app T).hom = _
  rw [F.map_comp, Category.assoc, Category.assoc]
  change _ ≫ _ ≫ ((groupBaseChange k K ⋙ F).map c ≫ n.hom.app T) = _
  rw [n.hom.naturality]
  simp only [← Category.assoc]
  have h : ((multiplicativeBaseChange K L).hom ≫ F.map (multiplicativeBaseChange k K).hom) ≫
      n.hom.app X = (multiplicativeBaseChange k L).hom := by
    change ((multiplicativeBaseChange K L).hom ≫ (groupBaseChange K L).map
      (multiplicativeBaseChange k K).hom) ≫
      ((groupBaseChangeTowerIso (k := k) (K := K) (L := L)).app
        (multiplicativeGroup k)).hom = _
    exact (Category.assoc _ _ _).trans (multiplicativeBaseChange_tower (k := k) (K := K) (L := L))
  exact congrArg (fun t ↦ t ≫ (groupBaseChange k L).map c) h

end ScalarTower

section GaloisTransport

open Opposite
open scoped CategoryTheory.MonoidalCategory CategoryTheory.MonObj
open private scalarIso twist twistGroups twistGroupBaseChangeIso
  from LinearAlgebraicGroups.Descent.FiniteFieldFlags

variable {K : Type u} [Field K] [Algebra k K]

private abbrev twistedBaseChange (σ : Gal(K/k)) (A : GroupScheme k) :=
  (twistGroupBaseChangeIso σ).app A

private theorem twistedBaseChange_hom_fst (σ : Gal(K/k)) (A : GroupScheme k) :
    (twistedBaseChange σ A).hom.hom.hom.left ≫ pullback.fst A.X.hom (fieldSpecMap k K) =
      pullback.fst A.X.hom (fieldSpecMap k K) := by
  exact pullback.lift_fst _ _ _

private theorem twistedBaseChange_hom_snd (σ : Gal(K/k)) (A : GroupScheme k) :
    (twistedBaseChange σ A).hom.hom.hom.left ≫ pullback.snd A.X.hom (fieldSpecMap k K) =
      pullback.snd A.X.hom (fieldSpecMap k K) ≫ (scalarIso σ).hom := by
  exact pullback.lift_snd _ _ _

private theorem twistedBaseChange_one (A : GroupScheme k) :
    (twistedBaseChange (1 : Gal(K/k)) A).hom.hom.hom.left = 𝟙 _ := by
  apply pullback.hom_ext
  · rw [twistedBaseChange_hom_fst, Category.id_comp]
  · rw [twistedBaseChange_hom_snd, Category.id_comp]
    have h : (scalarIso (1 : Gal(K/k))).hom = 𝟙 _ := Scheme.Spec.map_id _
    rw [h, Category.comp_id]

private theorem scalarIso_mul (σ τ : Gal(K/k)) :
    (scalarIso (σ * τ)).hom = (scalarIso σ).hom ≫ (scalarIso τ).hom := by
  change Spec.map (CommRingCat.ofHom (σ * τ).toRingHom) =
    Spec.map (CommRingCat.ofHom σ.toRingHom) ≫ Spec.map (CommRingCat.ofHom τ.toRingHom)
  rw [← Spec.map_comp]
  rfl

private theorem twistedBaseChange_mul (σ τ : Gal(K/k)) (A : GroupScheme k) :
    (twistedBaseChange (σ * τ) A).hom.hom.hom.left =
      (twistedBaseChange σ A).hom.hom.hom.left ≫ (twistedBaseChange τ A).hom.hom.hom.left := by
  apply pullback.hom_ext
  · rw [Category.assoc, twistedBaseChange_hom_fst, twistedBaseChange_hom_fst,
      twistedBaseChange_hom_fst]
  · rw [Category.assoc, twistedBaseChange_hom_snd, twistedBaseChange_hom_snd, ← Category.assoc,
      twistedBaseChange_hom_snd, scalarIso_mul, Category.assoc]

private theorem twistedBaseChange_inv (σ : Gal(K/k)) (A : GroupScheme k) :
    (twistedBaseChange σ A).inv.hom.hom.left =
      (twistedBaseChange σ⁻¹ A).hom.hom.hom.left := by
  let F := Grp.forget (SchemeOver K) ⋙ Over.forget (Spec (CommRingCat.of K))
  let e := F.mapIso (twistedBaseChange σ A)
  apply (Iso.cancel_iso_hom_left e _ _).mp
  change e.hom ≫ e.inv = _
  rw [e.hom_inv_id]
  change 𝟙 _ = (twistedBaseChange σ A).hom.hom.hom.left ≫
    (twistedBaseChange σ⁻¹ A).hom.hom.hom.left
  rw [← twistedBaseChange_mul, mul_inv_cancel, twistedBaseChange_one]
  rfl

private noncomputable def twistMorphism (σ : Gal(K/k)) {A B : GroupScheme k}
    (f : (groupBaseChange k K).obj A ⟶ (groupBaseChange k K).obj B) :
    (groupBaseChange k K).obj A ⟶ (groupBaseChange k K).obj B :=
  (twistedBaseChange σ A).inv ≫ (twistGroups σ).map f ≫ (twistedBaseChange σ B).hom

private theorem twistMorphism_one {A B : GroupScheme k}
    (f : (groupBaseChange k K).obj A ⟶ (groupBaseChange k K).obj B) :
    twistMorphism (1 : Gal(K/k)) f = f := by
  apply Grp.hom_ext
  apply Over.OverMorphism.ext
  change (twistedBaseChange (1 : Gal(K/k)) A).inv.hom.hom.left ≫
    f.hom.hom.left ≫ (twistedBaseChange (1 : Gal(K/k)) B).hom.hom.hom.left = _
  rw [twistedBaseChange_inv, inv_one, twistedBaseChange_one, twistedBaseChange_one]
  change (𝟙 ((groupBaseChange k K).obj A).X.left) ≫ f.hom.hom.left ≫
    𝟙 ((groupBaseChange k K).obj B).X.left = f.hom.hom.left
  rw [Category.id_comp, Category.comp_id]

private theorem twistMorphism_twistMorphism (σ τ : Gal(K/k)) {A B : GroupScheme k}
    (f : (groupBaseChange k K).obj A ⟶ (groupBaseChange k K).obj B) :
    twistMorphism σ (twistMorphism τ f) = twistMorphism (τ * σ) f := by
  apply Grp.hom_ext
  apply Over.OverMorphism.ext
  change (twistedBaseChange σ A).inv.hom.hom.left ≫
      ((twistedBaseChange τ A).inv.hom.hom.left ≫ f.hom.hom.left ≫
        (twistedBaseChange τ B).hom.hom.hom.left) ≫
      (twistedBaseChange σ B).hom.hom.hom.left =
    (twistedBaseChange (τ * σ) A).inv.hom.hom.left ≫ f.hom.hom.left ≫
      (twistedBaseChange (τ * σ) B).hom.hom.hom.left
  rw [twistedBaseChange_inv, twistedBaseChange_inv, twistedBaseChange_inv, mul_inv_rev,
    twistedBaseChange_mul, twistedBaseChange_mul]
  simp only [Category.assoc]

private noncomputable def twistCocharacter (σ : Gal(K/k)) {T : GroupScheme k}
    (c : Cocharacter ((groupBaseChange k K).obj T)) :
    Cocharacter ((groupBaseChange k K).obj T) :=
  (multiplicativeBaseChange k K).hom ≫ twistMorphism σ ((multiplicativeBaseChange k K).inv ≫ c)

private theorem twistCocharacter_one {T : GroupScheme k}
    (c : Cocharacter ((groupBaseChange k K).obj T)) :
    twistCocharacter (1 : Gal(K/k)) c = c := by
  rw [twistCocharacter, twistMorphism_one, Iso.hom_inv_id_assoc]

private theorem twistCocharacter_twistCocharacter (σ τ : Gal(K/k)) {T : GroupScheme k}
    (c : Cocharacter ((groupBaseChange k K).obj T)) :
    twistCocharacter σ (twistCocharacter τ c) = twistCocharacter (τ * σ) c := by
  unfold twistCocharacter
  rw [Iso.inv_hom_id_assoc, twistMorphism_twistMorphism]

section Multiplication

open scoped CategoryTheory.Obj

variable {T : GroupScheme k} [IsCommMonObj ((groupBaseChange k K).obj T).X]

private theorem twistCocharacter_mul (σ : Gal(K/k))
    (c d : Cocharacter ((groupBaseChange k K).obj T)) :
    twistCocharacter σ (c * d) = twistCocharacter σ c * twistCocharacter σ d := by
  apply Grp.hom_ext
  let M := multiplicativeGroup k
  let e := multiplicativeBaseChange k K
  let t := (twistedBaseChange σ M).inv.hom.hom
  let z := (twistedBaseChange σ T).hom.hom.hom
  let F := twist σ
  let a := e.inv.hom.hom
  let b := e.hom.hom.hom
  change b ≫ t ≫ F.map (a ≫ (c.hom.hom * d.hom.hom)) ≫ z =
    (b ≫ t ≫ F.map (a ≫ c.hom.hom) ≫ z) * (b ≫ t ≫ F.map (a ≫ d.hom.hom) ≫ z)
  rw [MonObj.comp_mul, Functor.map_mul, MonObj.mul_comp, MonObj.comp_mul,
    MonObj.comp_mul]

private theorem twistCocharacter_trivial (σ : Gal(K/k)) :
    twistCocharacter σ (1 : Cocharacter ((groupBaseChange k K).obj T)) = 1 := by
  apply Grp.hom_ext
  let M := multiplicativeGroup k
  let e := multiplicativeBaseChange k K
  let t := (twistedBaseChange σ M).inv.hom.hom
  let z := (twistedBaseChange σ T).hom.hom.hom
  let F := twist σ
  change e.hom.hom.hom ≫ t ≫ F.map (e.inv.hom.hom ≫ 1) ≫ z = 1
  rw [MonObj.comp_one, Functor.map_one, MonObj.one_comp, MonObj.comp_one, MonObj.comp_one]

@[instance_reducible] private noncomputable def galoisCocharacterAction :
    DistribMulAction Gal(K/k) (Additive (Cocharacter ((groupBaseChange k K).obj T))) where
  smul σ c := Additive.ofMul (twistCocharacter σ⁻¹ c.toMul)
  one_smul c := by
    change Additive.ofMul (twistCocharacter (1 : Gal(K/k))⁻¹ c.toMul) = c
    rw [inv_one, twistCocharacter_one]
    rfl
  mul_smul σ τ c := by
    change Additive.ofMul (twistCocharacter (σ * τ)⁻¹ c.toMul) =
      Additive.ofMul (twistCocharacter σ⁻¹ (twistCocharacter τ⁻¹ c.toMul))
    rw [mul_inv_rev, twistCocharacter_twistCocharacter]
  smul_add σ c d := congrArg Additive.ofMul (twistCocharacter_mul σ⁻¹ c.toMul d.toMul)
  smul_zero σ := congrArg Additive.ofMul (twistCocharacter_trivial σ⁻¹)

end Multiplication

/-- A field automorphism acts on the scalar-extended schemes by pullback
along the inverse automorphism of their base. -/
private noncomputable def automorphismPullbackIso (σ : Gal(K/k)) :
    Over.pullback (scalarIso σ).inv ≅ twist σ :=
  NatIso.ofComponents (fun X ↦ by
    let b := (scalarIso σ).inv
    letI : IsIso b := inferInstanceAs (IsIso (scalarIso σ).inv)
    refine Over.isoMk (asIso (pullback.fst X.hom b)) ?_
    change pullback.fst X.hom b ≫ X.hom ≫ (scalarIso σ).hom = pullback.snd X.hom b
    rw [← Category.assoc, pullback.condition, Category.assoc]
    change pullback.snd X.hom b ≫ (scalarIso σ).inv ≫ (scalarIso σ).hom = _
    rw [Iso.inv_hom_id, Category.comp_id]) (by
    intro X Y f
    apply Over.OverMorphism.ext
    change ((Over.pullback (scalarIso σ).inv).map f).left ≫ pullback.fst _ _ =
      pullback.fst _ _ ≫ f.left
    simp only [Over.pullback_map_left, pullback.lift_fst])

private noncomputable def automorphismGroupPullbackIso (σ : Gal(K/k)) :
    (Over.pullback (scalarIso σ).inv).mapGrp ≅ twistGroups σ :=
  Functor.mapGrpNatIso (automorphismPullbackIso σ)

private abbrev automorphismAlgebra (σ : Gal(K/k)) : Algebra K K :=
  σ.symm.toRingHom.toAlgebra

private theorem automorphismTower (σ : Gal(K/k)) :
    @IsScalarTower k K K inferInstance (automorphismAlgebra σ).toSMul inferInstance := by
  letI : Algebra K K := automorphismAlgebra σ
  exact IsScalarTower.of_algebraMap_eq (R := k) (S := K) (A := K) fun a ↦ by
    change algebraMap k K a = σ.symm (algebraMap k K a)
    exact (σ.symm.commutes a).symm

private theorem automorphismTowerComparison (σ : Gal(K/k)) (A : GroupScheme k) :
    letI : Algebra K K := automorphismAlgebra σ
    letI := automorphismTower σ
    (groupBaseChangeTowerIso (k := k) (K := K) (L := K)).app A =
      (automorphismGroupPullbackIso σ).app ((groupBaseChange k K).obj A) ≪≫
        twistedBaseChange σ A := by
  letI : Algebra K K := automorphismAlgebra σ
  letI := automorphismTower σ
  apply Iso.ext
  apply Grp.hom_ext
  apply Over.OverMorphism.ext
  apply pullback.hom_ext
  · change ((groupBaseChangeTowerIso (k := k) (K := K) (L := K)).app A).hom.hom.hom.left ≫
      pullback.fst A.X.hom (fieldSpecMap k K) =
      (pullback.fst ((baseChange k K).obj A.X).hom (fieldSpecMap K K) ≫
        (twistedBaseChange σ A).hom.hom.hom.left) ≫ pullback.fst A.X.hom (fieldSpecMap k K)
    rw [Category.assoc, twistedBaseChange_hom_fst, groupBaseChangeTowerIso_fst]
  · exact (Over.w _).trans (Over.w _).symm

private theorem twistCocharacter_eq_extend (σ : Gal(K/k)) {T : GroupScheme k}
    (c : Cocharacter ((groupBaseChange k K).obj T)) :
    letI : Algebra K K := automorphismAlgebra σ
    letI := automorphismTower σ
    extendCocharacter K c ≫
      ((groupBaseChangeTowerIso (k := k) (K := K) (L := K)).app T).hom =
      twistCocharacter σ c := by
  letI : Algebra K K := automorphismAlgebra σ
  letI := automorphismTower σ
  let F := groupBaseChange K K
  let M := multiplicativeGroup k
  let e := multiplicativeBaseChange k K
  let n := groupBaseChangeTowerIso (k := k) (K := K) (L := K)
  let v := automorphismGroupPullbackIso σ
  have hv := v.hom.naturality (e.inv ≫ c)
  change F.map (e.inv ≫ c) ≫ (v.app ((groupBaseChange k K).obj T)).hom =
    (v.app ((groupBaseChange k K).obj M)).hom ≫ (twistGroups σ).map (e.inv ≫ c) at hv
  have h₁ : (multiplicativeBaseChange K K).hom ≫ F.map e.hom ≫ (n.app M).hom = e.hom :=
    multiplicativeBaseChange_tower (k := k) (K := K) (L := K)
  have hM : (n.app M).hom = (v.app ((groupBaseChange k K).obj M)).hom ≫
      (twistedBaseChange σ M).hom :=
    congrArg Iso.hom (automorphismTowerComparison σ M)
  have hT : (n.app T).hom = (v.app ((groupBaseChange k K).obj T)).hom ≫
      (twistedBaseChange σ T).hom :=
    congrArg Iso.hom (automorphismTowerComparison σ T)
  have h₂ : (multiplicativeBaseChange K K).hom ≫ F.map e.hom ≫
      (v.app ((groupBaseChange k K).obj M)).hom = e.hom ≫ (twistedBaseChange σ M).inv := by
    apply (Iso.cancel_iso_hom_right _ _ (twistedBaseChange σ M)).mp
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    rw [← hM]
    exact h₁
  let p := (multiplicativeBaseChange K K).hom
  let c₀ := e.inv ≫ c
  have hc : e.hom ≫ c₀ = c := Iso.hom_inv_id_assoc e c
  change (p ≫ F.map c) ≫ (n.app T).hom =
    e.hom ≫ (twistedBaseChange σ M).inv ≫ (twistGroups σ).map c₀ ≫ (twistedBaseChange σ T).hom
  calc
    (p ≫ F.map c) ≫ (n.app T).hom =
        p ≫ F.map e.hom ≫ F.map c₀ ≫ (v.app ((groupBaseChange k K).obj T)).hom ≫
          (twistedBaseChange σ T).hom := by
      rw [← hc, F.map_comp, hT]
      simp only [Category.assoc]
    _ = p ≫ F.map e.hom ≫ (v.app ((groupBaseChange k K).obj M)).hom ≫
        (twistGroups σ).map c₀ ≫ (twistedBaseChange σ T).hom := by
      rw [← Category.assoc (F.map c₀), hv, Category.assoc]
    _ = _ := by
      simpa only [Category.assoc] using
        congrArg (fun j ↦ j ≫ (twistGroups σ).map c₀ ≫ (twistedBaseChange σ T).hom) h₂

end GaloisTransport

section ParabolicBaseChange

open Specs.Unipotent (baseChangedAlgebraicGroup)
open private pushSubgroup from LinearAlgebraicGroups.RootData.OrderedRootProducts
open private map_limit_parabolic from LinearAlgebraicGroups.RootData.RankOneFlag

variable {K L : Type u} [Field K] [Field L] [Algebra k K] [Algebra K L] [Algebra k L]
  [IsScalarTower k K L]

private theorem sameSubgroup_push_iff {G H : GroupScheme k} (e : G ≅ H)
    (A B : ClosedSubgroup G) :
    SameSubgroup (pushSubgroup e A) (pushSubgroup e B) ↔ SameSubgroup A B := by
  have h (S T : ClosedSubgroup G) :
      IsSubgroupOf (pushSubgroup e S) (pushSubgroup e T) ↔ IsSubgroupOf S T := by
    change (∃ j : S.group ⟶ T.group, j ≫ (T.inclusion ≫ e.hom) = S.inclusion ≫ e.hom) ↔ _
    constructor
    · rintro ⟨j, hj⟩
      exact ⟨j, (Iso.cancel_iso_hom_right _ _ e).mp (by simpa only [Category.assoc] using hj)⟩
    · rintro ⟨j, hj⟩
      exact ⟨j, by rw [← Category.assoc, hj]⟩
  exact and_congr (h A B) (h B A)

private theorem limitParabolic_transport {G : GroupScheme k} {c d : Cocharacter G}
    (h : c = d) (D : LimitDecomposition c) :
    (h ▸ D : LimitDecomposition d).parabolic = D.parabolic := by
  subst d
  rfl

private theorem pushLimitParabolic (G H : AffineAlgebraicGroup k)
    (e : G.val ≅ H.val) {c : Cocharacter G.val}
    (D : LimitDecomposition c) (E : LimitDecomposition (c ≫ e.hom)) :
    SameSubgroup (pushSubgroup e D.parabolic) E.parabolic := by
  refine ⟨map_limit_parabolic G.property.1 e.hom D E, ?_⟩
  have hh : (c ≫ e.hom) ≫ e.inv = c := by simp [Category.assoc]
  have h := map_limit_parabolic H.property.1 e.inv E (hh.symm ▸ D)
  rw [limitParabolic_transport] at h
  obtain ⟨j, hj⟩ := h
  refine ⟨j, ?_⟩
  change j ≫ D.parabolic.inclusion ≫ e.hom = _
  rw [← Category.assoc, hj, Category.assoc, e.inv_hom_id, Category.comp_id]

private theorem extendSubgroup_tower (G : GroupScheme k) (P : ClosedSubgroup G) :
    SameSubgroup
      (pushSubgroup ((groupBaseChangeTowerIso (K := K) (L := L)).app G)
        (extendSubgroup L (extendSubgroup K P)))
      (extendSubgroup L P) := by
  let n := groupBaseChangeTowerIso (k := k) (K := K) (L := L)
  let t := n.app P.group
  have hn : ((groupBaseChange k K ⋙ groupBaseChange K L).map P.inclusion) ≫ (n.app G).hom =
      t.hom ≫ (groupBaseChange k L).map P.inclusion := n.hom.naturality P.inclusion
  refine ⟨⟨t.hom, hn.symm⟩, ⟨t.inv, ?_⟩⟩
  change t.inv ≫ (((groupBaseChange k K ⋙ groupBaseChange K L).map P.inclusion) ≫ (n.app G).hom) = _
  rw [hn, t.inv_hom_id_assoc]
  rfl

private abbrev extendCocharacterInTower {T : GroupScheme k}
    (c : Cocharacter ((groupBaseChange k K).obj T)) :
    Cocharacter ((groupBaseChange k L).obj T) :=
  extendCocharacter L c ≫ ((groupBaseChangeTowerIso (K := K) (L := L)).app T).hom

private theorem sameParabolic_tower_iff (G : AffineAlgebraicGroup k)
    (P : ClosedSubgroup G.val) {T : GroupScheme k} (i : T ⟶ G.val)
    (c : Cocharacter ((groupBaseChange k K).obj T))
    (D : LimitDecomposition (c ≫ (groupBaseChange k K).map i))
    (E : LimitDecomposition
      (extendCocharacterInTower (L := L) c ≫ (groupBaseChange k L).map i)) :
    SameSubgroup (extendSubgroup K P) D.parabolic ↔
      SameSubgroup (extendSubgroup L P) E.parabolic := by
  let A := baseChangedAlgebraicGroup K G
  let B := baseChangedAlgebraicGroup L A
  let C := baseChangedAlgebraicGroup L G
  let n := groupBaseChangeTowerIso (k := k) (K := K) (L := L)
  let c' := c ≫ (groupBaseChange k K).map i
  obtain ⟨D'⟩ := existsLimitDecomposition B (extendCocharacter L c')
  have hm : extendCocharacter L c' ≫ (n.app G.val).hom =
    extendCocharacterInTower (L := L) c ≫ (groupBaseChange k L).map i := by
    change ((multiplicativeBaseChange K L).hom ≫
        (groupBaseChange K L).map (c ≫ (groupBaseChange k K).map i)) ≫ (n.app G.val).hom =
      (((multiplicativeBaseChange K L).hom ≫ (groupBaseChange K L).map c) ≫ (n.app T).hom) ≫
        (groupBaseChange k L).map i
    have hn : (groupBaseChange K L).map ((groupBaseChange k K).map i) ≫ (n.app G.val).hom =
      (n.app T).hom ≫ (groupBaseChange k L).map i := n.hom.naturality i
    rw [Functor.map_comp]
    simp only [Category.assoc, hn]
  have hE : SameSubgroup (pushSubgroup (n.app G.val) D'.parabolic) E.parabolic := by
    simpa only [limitParabolic_transport] using
      pushLimitParabolic B C (n.app G.val) D' (hm.symm ▸ E)
  have hD := (limits_subgroups_extend A D (multiplicativeBaseChange K L)
    (multiplicativeBaseChange_unit L) D').1
  have hP := extendSubgroup_tower (K := K) (L := L) G.val P
  have hp := sameSubgroup_push_iff (n.app G.val)
    (extendSubgroup L (extendSubgroup K P)) D'.parabolic
  constructor
  · intro h
    have h₁ := extend_subgroupOf (K := L) h.1
    have h₂ := extend_subgroupOf (K := L) h.2
    exact same_subgroup_trans (same_subgroup_symm hP)
      (same_subgroup_trans (hp.mpr (same_subgroup_trans ⟨h₁, h₂⟩ (same_subgroup_symm hD))) hE)
  · intro h
    have h' := same_subgroup_trans hP (same_subgroup_trans h (same_subgroup_symm hE))
    have h'' := same_subgroup_trans (hp.mp h') hD
    exact ⟨subgroupOf_of_extend h''.1, subgroupOf_of_extend h''.2⟩

end ParabolicBaseChange

section FiniteDescent

open Specs.CharacterDescent (StandardLattice)
open Opposite
open scoped TensorProduct MonoidAlgebra
open Specs.DiagonalizableGroups (groupAlgebra IntegerCharacters)
open private groupPresentation from LinearAlgebraicGroups.Affine.SchemeImageQuotient
open private extendedSpecIso extendedGroupIso extendedSpecIso_natural
  from LinearAlgebraicGroups.Affine.ClosedSubgroups
open private coefficientMap coefficientMap_spec twistGroups twistGroupBaseChangeIso
  from LinearAlgebraicGroups.Descent.FiniteFieldFlags
open private descendEquivariantHopfMap
  from LinearAlgebraicGroups.Multiplicative.CharacterDescent

variable {K : Type u} [Field K] [Algebra k K] [IsGalois k K]

/-- A Galois-invariant morphism of scalar extensions of affine groups descends. -/
private theorem descendInvariantGroupMorphism (A B : HopfAlgebraCategory k)
    (f : (groupBaseChange k K).obj (specGroup B) ⟶ (groupBaseChange k K).obj (specGroup A))
    (hf : ∀ σ : Gal(K/k), twistMorphism σ f = f) :
    ∃ g : specGroup B ⟶ specGroup A, (groupBaseChange k K).map g = f := by
  let a := extendedGroupIso K A
  let b := extendedGroupIso K B
  let F := hopfSpec.fullyFaithful (R := CommRingCat.of K)
  let v := F.preimage (b.hom ≫ f ≫ a.inv)
  have hv := F.map_preimage (b.hom ≫ f ≫ a.inv)
  let q := v.unop
  have hq : b.hom ≫ f = specGroupMap q ≫ a.hom := by
    have h : specGroupMap q = b.hom ≫ f ≫ a.inv := hv
    simp only [h, Category.assoc, Iso.inv_hom_id, Category.comp_id]
  have he : (LinearAlgebraicGroups.CharacterDescent.scalarExtensionDatum K A).Equivariant
      (LinearAlgebraicGroups.CharacterDescent.scalarExtensionDatum K B) q := by
    intro σ x
    let S := Grp.forget (SchemeOver K) ⋙ Over.forget (Spec (CommRingCat.of K))
    let d (D : HopfAlgebraCategory k) := (twistedBaseChange σ (specGroup D)).hom.hom.hom.left
    let e (D : HopfAlgebraCategory k) := (extendedSpecIso K D).hom.left
    let p (D : HopfAlgebraCategory k) :=
      Spec.map (CommRingCat.ofHom (coefficientMap σ D).toRingHom)
    let j := (specGroupMap q).hom.hom.left
    have hf' : (twistedBaseChange σ (specGroup B)).hom ≫ f =
        (twistGroups σ).map f ≫ (twistedBaseChange σ (specGroup A)).hom := by
      have hf' := congrArg ((twistedBaseChange σ (specGroup B)).hom ≫ ·) (hf σ)
      change (twistedBaseChange σ (specGroup B)).hom ≫
        ((twistedBaseChange σ (specGroup B)).inv ≫ (twistGroups σ).map f ≫
          (twistedBaseChange σ (specGroup A)).hom) =
        (twistedBaseChange σ (specGroup B)).hom ≫ f at hf'
      simpa only [Iso.hom_inv_id_assoc] using hf'.symm
    have hd : d B ≫ S.map f = S.map f ≫ d A := congrArg S.map (hf' : _ = _)
    have hsq : e B ≫ S.map f = j ≫ e A := congrArg S.map hq
    haveI : IsIso (e A) := (Over.forget _).map_isIso (extendedSpecIso K A).hom
    have hconj : p B ≫ j = j ≫ p A := by
      apply (cancel_mono (e A)).mp
      have hB : e B ≫ d B = p B ≫ e B := coefficientMap_spec σ B
      have hA : e A ≫ d A = p A ≫ e A := coefficientMap_spec σ A
      calc
        (p B ≫ j) ≫ e A = e B ≫ d B ≫ S.map f := by
          rw [Category.assoc, ← hsq, ← Category.assoc, ← hB, Category.assoc]
        _ = e B ≫ S.map f ≫ d A := by rw [hd]
        _ = (j ≫ p A) ≫ e A := by
          rw [← Category.assoc, hsq, Category.assoc, hA, Category.assoc]
    have hCoeff (D : HopfAlgebraCategory k) (y : K ⊗[k] D) :
        (LinearAlgebraicGroups.CharacterDescent.scalarExtensionDatum K D).action.act σ y =
          coefficientMap σ D y := by
      induction y using TensorProduct.inductionOn with
      | tmul r d => rfl
      | add u v hu hv => simp only [map_add, hu, hv]
    let fA := CommRingCat.ofHom (coefficientMap σ A).toRingHom
    let fB := CommRingCat.ofHom (coefficientMap σ B).toRingHom
    let qR := CommRingCat.ofHom q.hom.toAlgHom.toRingHom
    have hc : qR ≫ fB = fA ≫ qR := by
      apply Spec.map_injective
      rw [Spec.map_comp, Spec.map_comp]
      exact hconj
    have hr := congrArg CommRingCat.Hom.hom hc
    change (coefficientMap σ B).toRingHom.comp q.hom.toAlgHom.toRingHom =
      q.hom.toAlgHom.toRingHom.comp (coefficientMap σ A).toRingHom at hr
    rw [hCoeff A, hCoeff B]
    exact DFunLike.congr_fun hr.symm x
  obtain ⟨g, hg⟩ := descendEquivariantHopfMap K q he
  refine ⟨specGroupMap g, (Iso.cancel_iso_hom_left b _ _).mp ?_⟩
  have hnat : specGroupMap (extendedHopfMap K g) ≫ a.hom =
      b.hom ≫ (groupBaseChange k K).map (specGroupMap g) :=
    Grp.hom_ext _ _ (extendedSpecIso_natural K g)
  rw [← hnat, hg, ← hq]

private theorem descendInvariantCocharacter
    (T : AffineAlgebraicGroup k) (c : Cocharacter ((groupBaseChange k K).obj T.val))
    (hc : ∀ σ : Gal(K/k), twistCocharacter σ c = c) :
    ∃ d : Cocharacter T.val, extendCocharacter K d = c := by
  obtain ⟨A, _, ⟨e⟩⟩ := groupPresentation T
  let F := groupBaseChange k K
  let a := multiplicativeBaseChange k K
  let g := a.inv ≫ c ≫ F.map e.inv
  have hg (σ : Gal(K/k)) : twistMorphism σ g = g := by
    have h := (twistGroupBaseChangeIso σ).hom.naturality e.inv
    change (twistGroups σ).map (F.map e.inv) ≫ (twistedBaseChange σ (specGroup A)).hom =
      (twistedBaseChange σ T.val).hom ≫ F.map e.inv at h
    have hz : twistMorphism σ (a.inv ≫ c) = a.inv ≫ c := by
      have hz' := congrArg (a.inv ≫ ·) (hc σ)
      change a.inv ≫ (a.hom ≫ twistMorphism σ (a.inv ≫ c)) = a.inv ≫ c at hz'
      simpa only [Iso.inv_hom_id_assoc] using hz'
    change twistMorphism σ ((a.inv ≫ c) ≫ F.map e.inv) = (a.inv ≫ c) ≫ F.map e.inv
    calc
      _ = twistMorphism σ (a.inv ≫ c) ≫ F.map e.inv := by
        simp only [twistMorphism, Functor.map_comp, Category.assoc, h]
      _ = _ := congrArg (· ≫ F.map e.inv) hz
  obtain ⟨d, hd⟩ := descendInvariantGroupMorphism A (groupAlgebra k IntegerCharacters) g hg
  refine ⟨d ≫ e.hom, ?_⟩
  change a.hom ≫ F.map (d ≫ e.hom) = c
  rw [F.map_comp, hd]
  have he' : F.map e.inv ≫ F.map e.hom = 𝟙 _ := by
    rw [← F.map_comp, e.inv_hom_id, F.map_id]
  simp only [g, Category.assoc, Iso.hom_inv_id_assoc, he']
  change c ≫ 𝟙 ((groupBaseChange k K).obj T.val) = c
  exact Category.comp_id c

/-- A torus becomes diagonalizable over a finite Galois subfield of the
separable closure inside the algebraic closure. -/
private theorem torusFiniteDiagonalization (T : AffineAlgebraicGroup k) (hT : IsTorus T.val) :
    ∃ (E : IntermediateField k (separableClosure k (AlgebraicClosure k)))
      (_ : FiniteDimensional k E) (_ : IsGalois k E) (M : Specs.DiagonalizableGroups.FGAbelianGroup.{u}),
      Nonempty (specGroup (groupAlgebra E M.obj) ≅ (groupBaseChange k E).obj T.val) := by
  obtain ⟨A, _, ⟨a⟩⟩ := groupPresentation T
  obtain ⟨L, _, _, _, r, ⟨t⟩⟩ := hT
  obtain ⟨s⟩ := LinearAlgebraicGroups.CharacterDescent.standardSplitTorus (k := L) r
  let q := extendedGroupIso L A ≪≫ (groupBaseChange k L).mapIso a
  let e := (hopfSpec.fullyFaithful (R := CommRingCat.of L)).preimageIso (s ≪≫ t.symm ≪≫ q.symm)
  have hMT : Specs.CharacterDescent.IsMultiplicativeType A :=
    ⟨L, inferInstance, inferInstance, inferInstance,
      ⟨⟨CommGrpCat.of (StandardLattice.{u} r), inferInstance⟩, ⟨e.symm.unop⟩⟩⟩
  obtain ⟨E, hE, hGal, M, ⟨e⟩⟩ :=
    LinearAlgebraicGroups.CharacterDescent.finiteGaloisSplitting
      (K := separableClosure k (AlgebraicClosure k)) A hMT
  exact ⟨E, hE, hGal, M, ⟨(hopfSpec (CommRingCat.of E)).mapIso e.symm.op ≪≫
    extendedGroupIso E A ≪≫ (groupBaseChange k E).mapIso a⟩⟩

end FiniteDescent

section LeviAndRadical

open Specs.DiagonalizableGroups (IntegerCharacters groupAlgebra diagonalGroup)
open private latticeEquivOfBasis from LinearAlgebraicGroups.Multiplicative.SmoothnessAndIsogenies
open private isTorus_of_split from LinearAlgebraicGroups.Descent.FiniteFieldFlags
open private centralizes_comp_iff from LinearAlgebraicGroups.Reductive.CocharacterDynamics
open private reductive_of_groupIso same_subgroup_of_same_sections
  from LinearAlgebraicGroups.RootData.RankOneFlag
private theorem cocharacterImageIsTorus (H : AffineAlgebraicGroup k) (c : Cocharacter H.val) :
    ∃ (S : ClosedSubgroup H.val) (p : multiplicativeGroup k ⟶ S.group),
      IsTorus S.group ∧ p ≫ S.inclusion = c ∧ Flat p.hom.hom.left ∧ Surjective p.hom.hom.left := by
  let z : IntegerCharacters.{u} ≃* Multiplicative ℤ := MulEquiv.ulift
  letI : Group.FG IntegerCharacters.{u} :=
    Group.fg_of_surjective (f := z.symm.toMonoidHom) z.symm.surjective
  let M := diagonalGroup k IntegerCharacters.{u}
  obtain ⟨S, p, i, h, _, _⟩ := schemeImageFactorization M H c
  obtain ⟨N, ⟨e, _⟩, _⟩ := (LinearAlgebraicGroups.DiagonalizableGroups.diagonalFaithfullyFlatQuotients k
    IntegerCharacters.{u} ⟨S.val, S.property.1⟩ p).mp ⟨h.2.1, h.2.2.1⟩
  letI := LinearAlgebraicGroups.DiagonalizableGroups.subgroupFG N
  letI : Module.Finite ℤ (Additive N) := Module.Finite.iff_addGroup_fg.mpr inferInstance
  let f : Additive N →+ ℤ :=
    (z.toMonoidHom.comp N.subtype).toAdditive
  have hf : Function.Injective f := z.injective.comp Subtype.val_injective
  letI : Module.IsTorsionFree ℤ (Additive N) := by
    apply Module.IsTorsionFree.of_smul_eq_zero
    intro n x hx
    have hx' : n * f x = 0 := calc
      n * f x = n • f x := (zsmul_eq_mul _ _).symm
      _ = f (n • x) := (map_zsmul f n x).symm
      _ = 0 := by rw [hx, map_zero]
    exact (mul_eq_zero.mp hx').imp_right fun h₀ ↦ hf (h₀.trans f.map_zero.symm)
  obtain ⟨r, b⟩ := Module.basisOfFiniteTypeTorsionFree' (R := ℤ) (M := Additive N)
  let a := CommHopfAlgCat.isoMk (MonoidAlgebra.domCongrBialgEquiv k k (latticeEquivOfBasis b))
  let t := (hopfSpec (CommRingCat.of k)).mapIso a.op
  obtain ⟨j⟩ := LinearAlgebraicGroups.CharacterDescent.standardSplitTorus (k := k) r
  let U : ClosedSubgroup H.val := ⟨S.val, i, h.2.2.2.2.2⟩
  exact ⟨U, p, isTorus_of_split ⟨r, ⟨e.symm ≪≫ t.symm ≪≫ j⟩⟩, h.1, h.2.1, h.2.2.1⟩

/-- The centralizer of the cocharacter is the centralizer of its image subtorus. -/
private theorem cocharacterCentralizerReductive
    (G : AffineAlgebraicGroup k) (hG : IsReductive G)
    (T : ClosedSubgroup G.val) (hT : IsTorus T.group) (hTm : IsGeometricallyMaximal T)
    (c : Cocharacter T.group) (D : LimitDecomposition (c ≫ T.inclusion)) :
    IsReductive (closedSubgroupAlgebraicGroup D.centralizer) := by
  obtain ⟨S, p, hS, hp, hpf, hps⟩ :=
    cocharacterImageIsTorus (closedSubgroupAlgebraicGroup T) c
  let U := subgroupOfSubgroup T S
  obtain ⟨C, hC, hCr⟩ := LinearAlgebraicGroups.Reductive.SubtorusCentralizer.centralizerReductive
    G hG T U hT hS ⟨S.inclusion, rfl⟩
    hTm
  have hD : RepresentsSubgroup D.centralizer (fun _ g ↦ Centralizes U.inclusion g) := by
    intro X x
    letI := hpf
    letI := hps
    have hpx : p ≫ U.inclusion = c ≫ T.inclusion := by
      change p ≫ (S.inclusion ≫ T.inclusion) = c ≫ T.inclusion
      rw [← Category.assoc, hp]
    exact ((centralizes_comp_iff p U.inclusion x).symm.trans
      (hpx.symm ▸ D.centralizer_points X x))
  obtain ⟨e, _⟩ := subgroupIso_of_same (same_subgroup_of_same_sections (H := G) hC hD)
  exact reductive_of_groupIso e hCr

end LeviAndRadical

section RationalParabolic

open Specs.Unipotent (baseChangedAlgebraicGroup)
open private contracting_is_radical from LinearAlgebraicGroups.Flag.StandardParabolicLevi
open private isCommMonObj_of_groupIso from LinearAlgebraicGroups.Affine.HopfAlgebras

private def extendCocharacterAddHom {K L : Type u} [Field K] [Field L] [Algebra k K]
    [Algebra K L] [Algebra k L] [IsScalarTower k K L] {T : GroupScheme k}
    [IsCommMonObj ((groupBaseChange k K).obj T).X]
    [IsCommMonObj ((groupBaseChange k L).obj T).X] :
    Additive (Cocharacter ((groupBaseChange k K).obj T)) →+
      Additive (Cocharacter ((groupBaseChange k L).obj T)) where
  toFun c := Additive.ofMul (extendCocharacterInTower (L := L) c.toMul)
  map_zero' := by
    apply Additive.toMul.injective
    apply Grp.hom_ext
    let F := baseChange K L
    change ((multiplicativeBaseChange K L).hom.hom.hom ≫ F.map 1) ≫
      ((groupBaseChangeTowerIso (k := k) (K := K) (L := L)).app T).hom.hom.hom = 1
    rw [Functor.map_one, MonObj.comp_one, MonObj.one_comp]
  map_add' c d := by
    apply Additive.toMul.injective
    apply Grp.hom_ext
    let F := baseChange K L
    let e := (multiplicativeBaseChange K L).hom.hom.hom
    let n := ((groupBaseChangeTowerIso (k := k) (K := K) (L := L)).app T).hom.hom.hom
    let a := c.toMul.hom.hom
    let b := d.toMul.hom.hom
    change (e ≫ F.map (a * b)) ≫ n = ((e ≫ F.map a) ≫ n) * ((e ≫ F.map b) ≫ n)
    rw [Functor.map_mul, MonObj.comp_mul, MonObj.mul_comp]

/-- Construct the rational cocharacter by summing the Galois translates of
an integral cocharacter over a finite splitting field. -/
private theorem parabolicThroughGeometricTorus (classify : StandardParabolicClassification.{u})
    (G : AffineAlgebraicGroup k) (P : ClosedSubgroup G.val) (hP : IsParabolic G P)
    (T : ClosedSubgroup P.group) (hTk : IsTorus T.group) (hT : IsGeometricallyMaximal T) :
    ∃ (c : Cocharacter T.group) (D : LimitDecomposition (c ≫ (subgroupOfSubgroup P T).inclusion)),
      SameSubgroup P D.parabolic ∧
        IsReductive (closedSubgroupAlgebraicGroup D.centralizer) ∧ IsContractingRadical D := by
  classical
  let L := AlgebraicClosure k
  let F := groupBaseChange k L
  let Gbar := GeometricGroup G
  let Pbar := extendSubgroup L P
  let Tbar := extendSubgroup L T
  let S := subgroupOfSubgroup P T
  let Sbar := extendSubgroup L S
  have hSbar : subgroupOfSubgroup Pbar Tbar = Sbar := by
    change Specs.ClosedSubgroup.mk _ (F.map T.inclusion ≫ F.map P.inclusion) _ =
      Specs.ClosedSubgroup.mk _ (F.map (T.inclusion ≫ P.inclusion)) _
    congr 1
    exact (F.map_comp T.inclusion P.inclusion).symm
  obtain ⟨_, B, hB, hBP⟩ := hP.2.2
  have hGbar := reductive_geometricGroup G hP.1
  have hPs : Smooth Pbar.group.X.hom := smooth_baseChangedGroup hP.2.1
  obtain ⟨hSbarMax, B', hB', hTB', hB'P⟩ :=
    geometricBorelThroughTorus classify Gbar Pbar B hGbar hPs hB hBP Tbar hT.choose_spec
  rw [hSbar] at hSbarMax hTB'
  have hSbarSplit := split_of_maximal (A := Gbar) hSbarMax
  have hSbarGeom := geometricMaximal_of_maximal Gbar Sbar hSbarMax
  have hB'k := (isKBorel_iff_of_isAlgClosed Gbar B').mpr hB'
  have hPbar : IsParabolic Gbar Pbar :=
    ⟨hGbar, hPs, (extendSubgroup (AlgebraicClosure L) Pbar).isClosedImmersion,
      extendSubgroup (AlgebraicClosure L) B', hB'k.choose_spec, extend_subgroupOf hB'P⟩
  obtain ⟨a, A, hPA⟩ := splitParabolic classify Gbar Pbar Sbar B' hPbar hSbarSplit
    hSbarGeom hB'k hTB' hB'P
  let Talg := closedSubgroupAlgebraicGroup (G := closedSubgroupAlgebraicGroup P) T
  obtain ⟨K, hK, hGal, M, ⟨q⟩⟩ := torusFiniteDiagonalization Talg hTk
  letI := hK
  letI := hGal
  let incl : K →ₐ[k] L := (separableClosure k L).val.comp K.val
  letI : Algebra K L := incl.toRingHom.toAlgebra
  letI : IsScalarTower k K L := IsScalarTower.of_algebraMap_eq' incl.comp_algebraMap.symm
  letI : Fintype Gal(K/k) := Fintype.ofFinite _
  let i := S.inclusion
  let n := (groupBaseChangeTowerIso (k := k) (K := K) (L := L)).app T.group
  let Gmid := baseChangedAlgebraicGroup K G
  obtain ⟨b, hb⟩ := liftSplitCocharacter (T := (groupBaseChange k K).obj T.group)
    L q (multiplicativeBaseChange K L) (a ≫ n.inv)
  have hab : extendCocharacterInTower (K := K) (L := L) b = a := by
    change ((multiplicativeBaseChange K L).hom ≫ (groupBaseChange K L).map b) ≫ n.hom = a
    rw [hb, Category.assoc, n.inv_hom_id]
    exact Category.comp_id a
  obtain ⟨C⟩ := existsLimitDecomposition Gmid (b ≫ (groupBaseChange k K).map i)
  have hC : SameSubgroup (extendSubgroup K P) C.parabolic := by
    have h : ∀ (w : Cocharacter Sbar.group), (E : LimitDecomposition (w ≫ Sbar.inclusion)) →
        w = extendCocharacterInTower (K := K) (L := L) b →
        SameSubgroup Pbar E.parabolic → SameSubgroup (extendSubgroup K P) C.parabolic := by
      intro w E rfl h
      exact (sameParabolic_tower_iff G P i b C E).mpr h
    exact h a A hab.symm hPA
  letI : IsCommMonObj ((groupBaseChange k K).obj T.group).X :=
    isCommMonObj_of_groupIso q inferInstance
  letI : IsCommMonObj ((groupBaseChange k L).obj T.group).X := torus_commutative
    (closedSubgroupAlgebraicGroup (G := Gbar) Sbar) hSbarMax.1
  letI := galoisCocharacterAction (k := k) (K := K) (T := T.group)
  let up := extendCocharacterAddHom (k := k) (K := K) (L := L) (T := T.group)
  let orbitCocharacter (σ : Gal(K/k)) : Cocharacter ((groupBaseChange k K).obj T.group) :=
    (σ • Additive.ofMul b).toMul
  have horbit (σ : Gal(K/k)) :
      ∃ E : LimitDecomposition (extendCocharacterInTower (K := K) (L := L) (orbitCocharacter σ) ≫ Sbar.inclusion),
        SameSubgroup Pbar E.parabolic := by
    let τ := σ⁻¹
    obtain ⟨Dmid⟩ := existsLimitDecomposition Gmid (orbitCocharacter σ ≫ (groupBaseChange k K).map i)
    have hDmid : SameSubgroup (extendSubgroup K P) Dmid.parabolic := by
      letI : Algebra K K := automorphismAlgebra τ
      letI := automorphismTower τ
      have hγ : extendCocharacterInTower (k := k) (K := K) (L := K) b = orbitCocharacter σ :=
        twistCocharacter_eq_extend τ b
      have h : ∀ w : Cocharacter ((groupBaseChange k K).obj T.group),
          (E : LimitDecomposition (w ≫ (groupBaseChange k K).map i)) →
          w = extendCocharacterInTower (k := k) (K := K) (L := K) b →
          SameSubgroup (extendSubgroup K P) E.parabolic := by
        intro w E rfl
        exact (sameParabolic_tower_iff G P i b C E).mp hC
      exact h (orbitCocharacter σ) Dmid hγ.symm
    obtain ⟨E⟩ := existsLimitDecomposition Gbar (extendCocharacterInTower (L := L) (orbitCocharacter σ) ≫ Sbar.inclusion)
    exact ⟨E, (sameParabolic_tower_iff G P i (orbitCocharacter σ) Dmid E).mp hDmid⟩
  obtain ⟨z, hz, hsign⟩ := invariantIntegralSum (Γ := Gal(K/k)) (Additive.ofMul b)
  obtain ⟨_, _, _, _, _, pairingMap, _, hpairing⟩ :=
    LinearAlgebraicGroups.RootData.CharacterPairing.perfectCharacterPairing Sbar.group hSbarSplit
  have hsign' (α : absoluteRoots Sbar) :
      0 ≤ pairing Sbar.group α.val (up z).toMul ↔ 0 ≤ pairing Sbar.group α.val a := by
    let φ := (pairingMap (Additive.ofMul α.val)).toAddMonoidHom.comp up
    have hφ (x : Additive (Cocharacter ((groupBaseChange k K).obj T.group))) :
        φ x = pairing Sbar.group α.val (up x).toMul := hpairing α.val (up x).toMul
    have h := hsign φ
    simp only [hφ] at h
    rw [show (up (Additive.ofMul b)).toMul = a from hab] at h
    apply h
    intro σ
    obtain ⟨E, hE⟩ := horbit σ
    exact limitParabolic_signs_of_same Gbar Sbar _ _ E A
      (same_subgroup_trans (same_subgroup_symm hE) hPA) α
  obtain ⟨d, hd⟩ := descendInvariantCocharacter Talg z.toMul (fun σ ↦ by
    have h := hz σ⁻¹
    change Additive.ofMul (twistCocharacter σ⁻¹⁻¹ z.toMul) = z at h
    rw [inv_inv] at h
    exact congrArg Additive.toMul h)
  obtain ⟨D⟩ := existsLimitDecomposition G (d ≫ i)
  let dbar := extendCocharacter L d
  have hdb : (up z).toMul = dbar :=
    (congrArg (extendCocharacterInTower (K := K) (L := L)) hd).symm.trans (extendCocharacter_tower d)
  obtain ⟨E⟩ := existsLimitDecomposition Gbar (dbar ≫ Sbar.inclusion)
  have hE : SameSubgroup A.parabolic E.parabolic :=
    sameLimitParabolic_of_nonnegativeRoots Gbar hGbar Sbar hSbarSplit hSbarGeom a dbar A E
      (fun α ↦ by
        rw [← hdb]
        exact (hsign' α).symm)
  have hm : (dbar ≫ Sbar.inclusion) = extendCocharacter L (d ≫ i) := by
    change ((multiplicativeBaseChange k L).hom ≫ F.map d) ≫ F.map i =
      (multiplicativeBaseChange k L).hom ≫ F.map (d ≫ i)
    rw [F.map_comp, Category.assoc]
  let Dbar : LimitDecomposition (extendCocharacter L (d ≫ i)) := hm ▸ E
  have hDbar : SameSubgroup Pbar Dbar.parabolic := by
    change SameSubgroup Pbar (hm ▸ E : LimitDecomposition (extendCocharacter L (d ≫ i))).parabolic
    rw [limitParabolic_transport hm E]
    exact same_subgroup_trans hPA hE
  have hDP := (limits_subgroups_extend G D (multiplicativeBaseChange k L)
    (multiplicativeBaseChange_unit L) Dbar).1
  have hp := same_subgroup_trans hDbar hDP
  have hSm : IsGeometricallyMaximal S := ⟨Sbar.isClosedImmersion, hSbarMax⟩
  have hLev := cocharacterCentralizerReductive G hP.1 S hTk hSm d D
  letI := hP.1.1
  letI : ConnectedSpace G.val.X.left := connected_of_geometricallyConnected hP.1.2.1
  refine ⟨d, D, ⟨subgroupOf_of_extend hp.1, subgroupOf_of_extend hp.2⟩, hLev, ?_⟩
  apply contracting_is_radical (G := G) D hLev (limitSubgroupsSmooth G _ D).2.1
    (geometricallyConnectedLimitSubgroups G _ D).2.1
  obtain ⟨U, e, hU⟩ := contractingSubgroupUnipotent G _ D
  exact ⟨U, e, hU⟩

/-- The defining cocharacter may be chosen in any prescribed maximal
   ground-field torus of the parabolic. -/
theorem rationalParabolicThroughTorus : Specs.RationalCocharacter.RationalParabolicThroughTorus.{u} := by
  intro k _ G P hP T hT
  have classify : StandardParabolicClassification.{u} :=
    @LinearAlgebraicGroups.Flag.StandardParabolics.standardParabolicClassification.{u}
  exact parabolicThroughGeometricTorus classify G P hP T hT.1
    (geometricMaximal_of_rationalMaximal (closedSubgroupAlgebraicGroup P) hP.2.1
      (parabolicConnected classify G P hP) T hT)

/-- A rational parabolic has a cocharacter limit presentation, with the
centralizer as reductive Levi and the contracting subgroup as radical. -/
theorem rationalParabolic : Specs.RationalCocharacter.RationalParabolic.{u} := by
  intro k _ G P hP
  have classify : StandardParabolicClassification.{u} :=
    @LinearAlgebraicGroups.Flag.StandardParabolics.standardParabolicClassification.{u}
  obtain ⟨T, hT, hTm⟩ := MaximalToriExist.geometricallyMaximalTorusExists
    (closedSubgroupAlgebraicGroup P) hP.2.1 (parabolicConnected classify G P hP)
  obtain ⟨c, D, hD⟩ := parabolicThroughGeometricTorus classify G P hP T hT hTm
  exact ⟨c ≫ (subgroupOfSubgroup P T).inclusion, D, hD⟩

end RationalParabolic

end

end LinearAlgebraicGroups.Relative.RationalCocharacter
