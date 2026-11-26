import Specs.LinearAlgebraicGroups.Arithmetic.ExceptionalAdaptedRationalOppositePair
import LinearAlgebraicGroups.Arithmetic.QuasiSplitFixedWeyl
import LinearAlgebraicGroups.Arithmetic.QuasiSplitPinnedPairModel
import LinearAlgebraicGroups.Relative.SplitContractingRadical
import Batteries.Tactic.OpenPrivate

open AlgebraicGeometry CategoryTheory

universe u

namespace LinearAlgebraicGroups.Arithmetic.ExceptionalAdaptedRationalOppositePair

open LinearAlgebraicGroups.Specs
open Specs.BorelsAndChambers (IsRegular contractingSubgroup)
open Specs.CharacterDescent (Cocharacter)
open Specs.GeometricBorelConjugacy (IsBorel IsKBorel)
open Specs.GeometricRadicals
  (GeometricGroup IsMaximalTorus IsReductive IsSplitTorus IsUnipotentRadical)
open Specs.QuasiSplitPinnedPairModel (BorelPair)
open Specs.RankOneFlag (IsGeometricallyMaximal SameSubgroup)
open Specs.SchemeDerivedGroup (IsSubgroupOf)
open Specs.Unipotent (IsUnipotent closedSubgroupAlgebraicGroup)
open LinearAlgebraicGroups.CocharacterDynamics
  (LimitDecomposition existsLimitDecomposition oppositeCocharacter)
open LinearAlgebraicGroups.Relative.SplitContractingRadical (contractingSubgroupIsRadical)

open private borelDefiningCocharacter
  from LinearAlgebraicGroups.Arithmetic.QuasiSplitFixedWeyl
open private limitBorelIntersection from LinearAlgebraicGroups.Arithmetic.QuasiSplitPinnedPairModel
open private extendSubgroup isBorel_of_same isKBorel_iff_of_isAlgClosed split_of_maximal
  subgroup_extend geometricMaximal_of_maximal
  from LinearAlgebraicGroups.RootData.BorelNormalizer
open private reductive_geometricGroup regular_of_centralizer from LinearAlgebraicGroups.RootData.BorelsAndChambers
open private centralizes_opposite_iff opposite_baseChange limits_subgroups_extend
  same_subgroup_of_same_sections same_subgroup_trans from LinearAlgebraicGroups.RootData.RankOneFlag
open private extendCocharacter multiplicativeBaseChange multiplicativeBaseChange_unit
  from LinearAlgebraicGroups.Relative.RationalCocharacter
open private sameSubgroupIso from LinearAlgebraicGroups.Classification.CentralIsogenies
open private transportSubgroup radical_transport unipotent_of_iso
  from LinearAlgebraicGroups.Reductive.RadicalBaseChange

noncomputable section

set_option backward.isDefEq.respectTransparency false in
private theorem extendOppositeCocharacter {k K : Type u} [Field k] [Field K] [Algebra k K]
    {G H : GroupScheme k} (c : Cocharacter H) (i : H ⟶ G) :
    extendCocharacter K (oppositeCocharacter (c ≫ i)) =
      oppositeCocharacter (extendCocharacter K c) ≫ (groupBaseChange k K).map i := by
  change (multiplicativeBaseChange k K).hom ≫
      (groupBaseChange k K).map (oppositeCocharacter (c ≫ i)) =
    oppositeCocharacter ((multiplicativeBaseChange k K).hom ≫
      (groupBaseChange k K).map c) ≫ (groupBaseChange k K).map i
  rw [← opposite_baseChange _ _ (multiplicativeBaseChange_unit K)]
  unfold oppositeCocharacter
  rw [Functor.map_comp, Category.assoc, Category.assoc]

set_option backward.isDefEq.respectTransparency false in
private theorem oppositeCentralizer {k : Type u} [Field k] (G : AffineAlgebraicGroup k)
    (T : ClosedSubgroup G.val) {c : Cocharacter G.val}
    (hT : RepresentsSubgroup T (fun _ g ↦ Centralizes c g))
    (E : LimitDecomposition (oppositeCocharacter c)) :
    SameSubgroup E.centralizer T := by
  have hOpposite : RepresentsSubgroup T (fun _ g ↦ Centralizes (oppositeCocharacter c) g) :=
    fun Y g ↦ (centralizes_opposite_iff c g).trans (hT Y g)
  exact same_subgroup_of_same_sections (H := G) E.centralizer_points hOpposite

set_option backward.isDefEq.respectTransparency false in
private theorem geometricLimitIsBorel {k : Type u} [Field k] [IsAlgClosed k]
    (G : AffineAlgebraicGroup k) (hG : IsReductive G)
    (T : ClosedSubgroup G.val) (hMax : IsMaximalTorus T)
    (c : Cocharacter T.group) {d : Cocharacter G.val} (D : LimitDecomposition d)
    (hd : d = c ≫ T.inclusion) (hZ : SameSubgroup D.centralizer T) :
    IsBorel D.parabolic := by
  subst d
  have hSplit := split_of_maximal (A := G) hMax
  have hMax' := geometricMaximal_of_maximal G T hMax
  have hRegular : IsRegular T c := regular_of_centralizer G hG T hSplit hMax' c D hZ
  have hBorel := (RootData.BorelsAndChambers.regularCocharacterBorel G hG T hSplit hMax'
    c hRegular D).2.1
  exact (isKBorel_iff_of_isAlgClosed G D.parabolic).mp hBorel

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 150000 in
private theorem oppositeLimitIsKBorel {k : Type u} [Field k] (G : AffineAlgebraicGroup k)
    (hG : IsReductive G) (T : ClosedSubgroup G.val) (hTm : IsGeometricallyMaximal T)
    (c : Cocharacter T.group) (E : LimitDecomposition (oppositeCocharacter (c ≫ T.inclusion)))
    (hZ : SameSubgroup E.centralizer T) : IsKBorel E.parabolic := by
  let K := AlgebraicClosure k
  let G' := GeometricGroup G
  let T' : ClosedSubgroup G'.val := extendSubgroup K T
  have hMax : IsMaximalTorus T' := hTm.choose_spec
  obtain ⟨E'⟩ := existsLimitDecomposition G'
    (extendCocharacter K (oppositeCocharacter (c ≫ T.inclusion)))
  have he : extendCocharacter K (oppositeCocharacter (c ≫ T.inclusion)) =
      oppositeCocharacter (extendCocharacter K c) ≫ T'.inclusion :=
    extendOppositeCocharacter c T.inclusion
  have hBase := limits_subgroups_extend G E (multiplicativeBaseChange k K)
    (multiplicativeBaseChange_unit K) E'
  have hZT : SameSubgroup (extendSubgroup K E.centralizer) T' :=
    ⟨subgroup_extend K hZ.1, subgroup_extend K hZ.2⟩
  have hZ' : SameSubgroup E'.centralizer T' := same_subgroup_trans hBase.2.2 hZT
  have hBorel : IsBorel E'.parabolic :=
    geometricLimitIsBorel G' (reductive_geometricGroup G hG) T' hMax
      (oppositeCocharacter (extendCocharacter K c)) E' he hZ'
  exact ⟨(extendSubgroup K E.parabolic).isClosedImmersion,
    isBorel_of_same (A := G') hBase.1 hBorel⟩

set_option backward.isDefEq.respectTransparency false in
private theorem radicalOfLimitBorel {k : Type u} [Field k] (G : AffineAlgebraicGroup k)
    (hG : IsReductive G) (B : ClosedSubgroup G.val)
    {c : Cocharacter G.val} (D : LimitDecomposition c)
    (hB : SameSubgroup B D.parabolic) :
    ∃ U : ClosedSubgroup B.group, IsUnipotentRadical (closedSubgroupAlgebraicGroup B) U := by
  obtain ⟨e, _⟩ := sameSubgroupIso hB
  let U := contractingSubgroup D
  have hU : IsUnipotentRadical (closedSubgroupAlgebraicGroup D.parabolic) U :=
    (contractingSubgroupIsRadical G hG c D).1
  refine ⟨transportSubgroup e.symm U, ?_⟩
  exact radical_transport (G := closedSubgroupAlgebraicGroup D.parabolic)
    (G' := closedSubgroupAlgebraicGroup B) e.symm IsUnipotent
    (fun {H J} i _ _ ↦ unipotent_of_iso (G := closedSubgroupAlgebraicGroup H)
      (H := closedSubgroupAlgebraicGroup J) i) U hU

set_option backward.isDefEq.respectTransparency false in
/-- The ground-field Borel pair with the prescribed positive Borel and torus. -/
theorem rationalOppositePair : Specs.ExceptionalAdaptedRationalOppositePair.Statement.{u} := by
  intro k _ G hG B T hB hT hMax hTB
  obtain ⟨c, D, hBD, hC⟩ := borelDefiningCocharacter G hG B T hB hT hMax hTB
  let d := oppositeCocharacter (c ≫ T.inclusion)
  obtain ⟨E⟩ := existsLimitDecomposition G d
  have hSame : SameSubgroup E.centralizer T := oppositeCentralizer G T hC E
  have hE : IsKBorel E.parabolic := oppositeLimitIsKBorel G hG T hMax c E hSame
  have hTE : IsSubgroupOf T E.parabolic := by
    obtain ⟨j, hj⟩ := hSame.2
    exact ⟨j ≫ E.sectionMap, by rw [Category.assoc, E.section_in_G, hj]⟩
  obtain ⟨U, hU⟩ := radicalOfLimitBorel G hG B D hBD
  let P : BorelPair G :=
    { positive := B
      negative := E.parabolic
      torus := T
      positiveRadical := U
      negativeRadical := contractingSubgroup E
      positiveBorel := hB
      negativeBorel := hE
      isTorus := hT
      maximal := hMax
      intersection := limitBorelIntersection G T B D E hBD hSame hTB hTE
      positiveUnipotentRadical := hU
      negativeUnipotentRadical := (contractingSubgroupIsRadical G hG d E).1 }
  exact ⟨P, rfl, rfl⟩

end

end LinearAlgebraicGroups.Arithmetic.ExceptionalAdaptedRationalOppositePair
