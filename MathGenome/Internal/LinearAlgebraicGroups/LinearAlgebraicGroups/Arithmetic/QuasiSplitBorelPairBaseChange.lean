import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Arithmetic.QuasiSplitBorelPairBaseChange
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Affine.Stabilizers
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Descent.BorelInnerAlignment
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Reductive.CentralFrobeniusDescent
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Reductive.RadicalBaseChange
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Reductive.TorusCentralizer
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.RootData.RankOneFlag
import Batteries.Tactic.OpenPrivate

open AlgebraicGeometry CategoryTheory
open CategoryTheory.MonoidalCategory

universe u

namespace LinearAlgebraicGroups.Arithmetic.QuasiSplitBorelPairBaseChange

open _root_.LinearAlgebraicGroups.Specs
open Specs.GeometricBorelConjugacy (IsKBorel)
open Specs.GeometricRadicals (GeometricGroup IsReductive IsTorus IsSplitTorus
  IsMaximalTorus)
open Specs.QuasiSplitBorelPairBaseChange (ExtendBorelPair)
open Specs.RankOneFlag (IsGeometricallyMaximal SameSubgroup)
open Specs.SubtorusCentralizer (IsCentralizer)
open Specs.Unipotent (baseChangedAlgebraicGroup closedSubgroupAlgebraicGroup)
open Specs.UnipotentRadicalIntersection (IsSchemeIntersection)

open private extendedBorel from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Descent.BorelInnerAlignment
open private groupBaseChangeTower extendSubgroup
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Reductive.RadicalBaseChange
open private borelUnderIso from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Relative.ParabolicIntersection
open private transportSubgroup from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Reductive.MaximalToriConjugate
open private isBorel_of_same from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.RootData.BorelNormalizer
open private lattice_torus_of_split from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.RootData.RankOneFlag
open private torus_baseChange_algClosure from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Reductive.SubtorusCentralizer
open private centralizes_iff from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Affine.Stabilizers
open private isMonHom_of_factor from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Solvable.FiniteWordClosure
open scoped CategoryTheory.MonObj

noncomputable section

set_option backward.isDefEq.respectTransparency false

variable {k K : Type u} [Field k] [Field K] [Algebra k K]

private theorem borel_baseChange (G : AffineAlgebraicGroup k) (hG : IsReductive G)
    (B : ClosedSubgroup G.val) (hB : IsKBorel B) : IsKBorel (extendSubgroup K B) := by
  let L := AlgebraicClosure K
  let BK := extendSubgroup K B
  let BL := extendSubgroup L B
  let BKL := extendSubgroup L BK
  let e := groupBaseChangeTower (k := k) (K := K) L
  let f := e.app B.group
  let g := e.app G.val
  have h : BL.inclusion ≫ g.hom = f.hom ≫ BKL.inclusion :=
    e.hom.naturality B.inclusion
  have hsame : SameSubgroup (transportSubgroup g BL) BKL := by
    refine ⟨⟨f.hom, h.symm⟩, ⟨f.inv, ?_⟩⟩
    change f.inv ≫ (BL.inclusion ≫ g.hom) = BKL.inclusion
    rw [h, Iso.inv_hom_id_assoc]
  exact ⟨BKL.isClosedImmersion,
    isBorel_of_same (A := GeometricGroup (baseChangedAlgebraicGroup K G)) hsame
      (borelUnderIso g (extendedBorel G hG B hB L))⟩

private theorem maximal_of_selfCentralizing {G : AffineAlgebraicGroup k}
    (T : ClosedSubgroup G.val) (hT : IsTorus T.group)
    (hcentralizer : IsCentralizer T T) : IsMaximalTorus T := by
  refine ⟨hT, ?_⟩
  rintro S hS ⟨j, hj⟩
  have hj' : j.hom.hom ≫ S.inclusion.hom.hom = T.inclusion.hom.hom :=
    congrArg (Grp.forget (SchemeOver k)).map hj
  have hcomm : IsCommMonObj S.group.X :=
    CentralFrobeniusDescent.torus_commutative (closedSubgroupAlgebraicGroup S) hS
  have hcentralizes := (centralizes_iff T.inclusion S.inclusion.hom.hom).mpr (by
    intro U a b
    rw [← hj', ← Category.assoc b]
    let := (isCommMonObj_iff_isMulCommutative S.group.X).mp hcomm U
    exact (commute_iff_eq _ _).mpr (by simp only [← MonObj.mul_comp, mul_comm']))
  obtain ⟨f, hf⟩ := (hcentralizer _ _).mp hcentralizes
  let := T.isClosedImmersion
  let : Mono T.inclusion.hom.hom := Over.mono_of_mono_left _
  let := isMonHom_of_factor S.inclusion T.inclusion f hf
  exact ⟨Grp.homMk f, Grp.hom_ext _ _ hf⟩

private theorem geometricallyMaximal_baseChange (G : AffineAlgebraicGroup k)
    (hG : IsReductive G) (T : ClosedSubgroup G.val) (hT : IsTorus T.group)
    (hmax : IsGeometricallyMaximal T)
    (hsplit : IsSplitTorus ((groupBaseChange k K).obj T.group)) :
    IsGeometricallyMaximal (extendSubgroup K T) := by
  let L := AlgebraicClosure K
  let TK := extendSubgroup K T
  let TL := extendSubgroup L TK
  have h := Reductive.TorusCentralizer.maximalTorusCentralizer G hG T hT hmax
  obtain ⟨_, hK⟩ := LinearAlgebraicGroups.centralizerSchemeBaseChange k K T.inclusion T h
  obtain ⟨_, hL⟩ :=
    LinearAlgebraicGroups.centralizerSchemeBaseChange K L TK.inclusion TK hK
  have hTK : IsTorus TK.group := lattice_torus_of_split hsplit
  have hTL : IsTorus TL.group :=
    torus_baseChange_algClosure (closedSubgroupAlgebraicGroup
      (G := baseChangedAlgebraicGroup K G) TK) hTK
  exact ⟨TL.isClosedImmersion, maximal_of_selfCentralizing
    (G := GeometricGroup (baseChangedAlgebraicGroup K G)) TL hTL hL⟩

/-- Restriction along the field map transfers the subgroup factorization of
a section by the slice adjunction. -/
private theorem mem_extendSubgroup_iff {G : GroupScheme k} (H : ClosedSubgroup G)
    (Y : SchemeOver K) (y : Y ⟶ ((groupBaseChange k K).obj G).X) :
    y ∈ SubgroupSections (extendSubgroup K H) Y ↔
      ((Over.mapPullbackAdj (fieldSpecMap k K)).homEquiv Y G.X).symm y ∈
        SubgroupSections H ((Over.map (fieldSpecMap k K)).obj Y) := by
  let adj := Over.mapPullbackAdj (fieldSpecMap k K)
  change (∃ z : Y ⟶ (baseChange k K).obj H.group.X,
    z ≫ (baseChange k K).map H.inclusion.hom.hom = y) ↔
      ∃ z : (Over.map (fieldSpecMap k K)).obj Y ⟶ H.group.X,
        z ≫ H.inclusion.hom.hom = (adj.homEquiv Y G.X).symm y
  constructor
  · rintro ⟨z, rfl⟩
    exact ⟨(adj.homEquiv Y H.group.X).symm z,
      (adj.homEquiv_naturality_right_symm z H.inclusion.hom.hom).symm⟩
  · rintro ⟨z, hz⟩
    exact ⟨adj.homEquiv Y H.group.X z, by
      rw [← adj.homEquiv_naturality_right, hz, Equiv.apply_symm_apply]⟩

private theorem intersection_baseChange {G : GroupScheme k} (B C T : ClosedSubgroup G)
    (h : IsSchemeIntersection {B, C} T) :
    IsSchemeIntersection {extendSubgroup K B, extendSubgroup K C} (extendSubgroup K T) := by
  intro Y y
  simpa only [Set.mem_insert_iff, Set.mem_singleton_iff, forall_eq_or_imp, forall_eq,
    mem_extendSubgroup_iff] using
    h ((Over.map (fieldSpecMap k K)).obj Y)
      (((Over.mapPullbackAdj (fieldSpecMap k K)).homEquiv Y G.X).symm y)

/-- Scalar extension preserves the marked opposite Borel pair and its common
geometrically maximal torus, with their inclusions into the extended group. -/
theorem extendBorelPair : ExtendBorelPair.{u} := by
  intro k K _ _ _ G hG B C T hB hC hT hmax hinter hsplit
  exact ⟨(extendSubgroup K B).isClosedImmersion, (extendSubgroup K C).isClosedImmersion,
    (extendSubgroup K T).isClosedImmersion,
    (Reductive.RadicalBaseChange.reductiveFieldExtension G hG.1 hG.2.1).mpr hG,
    borel_baseChange G hG B hB, borel_baseChange G hG C hC,
    geometricallyMaximal_baseChange G hG T hT hmax hsplit,
    intersection_baseChange B C T hinter⟩

end

end LinearAlgebraicGroups.Arithmetic.QuasiSplitBorelPairBaseChange
