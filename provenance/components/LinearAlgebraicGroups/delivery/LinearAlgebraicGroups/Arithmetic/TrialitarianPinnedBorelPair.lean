import Specs.LinearAlgebraicGroups.Arithmetic.TrialitarianPinnedBorelPair
import LinearAlgebraicGroups.Arithmetic.QuasiSplitLocalGeneration
import LinearAlgebraicGroups.Classification.TransportedRootCoordinates
import LinearAlgebraicGroups.Descent.RelativeFormComparison
import Batteries.Tactic.OpenPrivate

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open scoped CategoryTheory.MonObj

universe u

namespace LinearAlgebraicGroups.Arithmetic.TrialitarianPinnedBorelPair

open _root_.LinearAlgebraicGroups.Specs
open Specs.Arithmetic.TrialitarianPinnedBorelPair
open Specs.AutomorphismSequence (AdjointQuotient RelativeAut SplitSequence relativePoints)
open Specs.CharacterDescent (Cocharacter)
open Specs.GeometricBorelConjugacy (IsKBorel IsQuasiSplit)
open Specs.GeometricRadicals (IsReductive IsSemisimple IsTorus IsUnipotentRadical GeometricGroup)
open Specs.Pinning (AttachedDatum PinnedGroup SplitBorelPair)
open Specs.QuasiSplitInnerForms
  (PinnedRepresentative mapCocycle mapH1 outerHom trivialOuterAction)
open Specs.QuasiSplitPinnedPairModel (BorelPair MarkedComparison MatchesCoordinateComparison)
open Specs.QuasiSplitOrbitLevis (SplitPairOver)
open Specs.RankOneFlag (IsGeometricallyMaximal SameSubgroup)
open Specs.RelativeFormComparison (fieldTest transportedAut)
open Specs.RootGroups (AdditiveLine rootPoint)
open Specs.SchemeDerivedGroup (IsSubgroupOf)
open Specs.Unipotent (baseChangedAlgebraicGroup closedSubgroupAlgebraicGroup)
open CocharacterDynamics (existsLimitDecomposition LimitDecomposition oppositeCocharacter)
open RootData.BorelsAndChambers (regularCocharacterBorel)
open Descent.NonabelianCohomology (classOf restriction)
open Descent.Forms (SchemeModels)
open Descent.RelativeFormComparison (relativeFormClassification)
open private pinnedRepresentatives quasiSplitUniqueness pinnedClass
  from LinearAlgebraicGroups.Descent.QuasiSplitInnerForms
open private reductive_of_semisimple from LinearAlgebraicGroups.Classification.CentralIsogenies
open private transportSubgroup from LinearAlgebraicGroups.Reductive.MaximalToriConjugate
open private pushKBorel maximalTransport from LinearAlgebraicGroups.Classification.PinnedEquivalence
open private basedLift_of_splitSequence transportPinnedTwist
  from LinearAlgebraicGroups.Arithmetic.QuasiSplitPinnedPairModel
open private borelDefiningCocharacter regularAtSplittingField sameSubgroupOfCentralizer
  from LinearAlgebraicGroups.Arithmetic.QuasiSplitFixedWeyl
open private extendCocharacter multiplicativeBaseChange multiplicativeBaseChange_unit
  from LinearAlgebraicGroups.Relative.RationalCocharacter
open private extendSubgroup from LinearAlgebraicGroups.Reductive.RadicalBaseChange
open private centralizes_opposite_iff limits_subgroups_extend opposite_baseChange borel_of_same
  from LinearAlgebraicGroups.RootData.RankOneFlag
open private opposite_regular from LinearAlgebraicGroups.Flag.StandardParabolics
open private split_of_maximal isKBorel_iff_of_isAlgClosed from LinearAlgebraicGroups.RootData.BorelNormalizer
open private reductive_geometricGroup from LinearAlgebraicGroups.RootData.BorelsAndChambers
open private limitBorelIntersection from LinearAlgebraicGroups.Arithmetic.QuasiSplitPinnedPairModel
open private borelRadicalAndQuotient from LinearAlgebraicGroups.Arithmetic.QuasiSplitOrbitLevis

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false

variable {F Fsep : Type u} [Field F] [Field Fsep] [Algebra F Fsep] [IsSepClosure F Fsep]
  {G : AffineAlgebraicGroup F} {A₀ : AdditiveLine F} {P₀ : PinnedGroup A₀}
  {D₀ : AttachedDatum P₀.pair} {l : Aut D₀.toBased ≃* Aut P₀}
  {Q : AdjointQuotient P₀.pair.G}

local instance (D : Specs.Pinning.BasedRootDatum.{u}) : TopologicalSpace (Aut D) := ⊥
local instance (D : Specs.Pinning.BasedRootDatum.{u}) : DiscreteTopology (Aut D) := ⟨rfl⟩
local instance : TopologicalSpace (Gal(Fsep/F)) := krullTopology F Fsep

local instance (J : GroupScheme F) :
    TopologicalSpace (RelativeAut J (fieldTest F Fsep)) := ⊥

local instance (J : GroupScheme F) :
    DiscreteTopology (RelativeAut J (fieldTest F Fsep)) := ⟨rfl⟩

set_option maxHeartbeats 1200000 in
/-- Use the given trivialization to select the outer cocycle of the pinned
representative. Its ground-field isomorphism to the given form follows from
quasi-split uniqueness. -/
private theorem pinnedRepresentativeOfTrivialization
    (hG : IsQuasiSplit G) (E : SplitSequence P₀ D₀ l Q)
    (f : (groupBaseChange F Fsep).obj P₀.pair.G.val ≅ (groupBaseChange F Fsep).obj G.val)
    (i : relativePoints P₀.pair.G.val (fieldTest F Fsep) ≅ relativePoints G.val (fieldTest F Fsep)) :
    ∃ (ω : Descent.NonabelianCohomology.Cocycle
        (trivialOuterAction (k := F) (S := Fsep) D₀.toBased))
      (W : PinnedRepresentative (S := Fsep) E ω),
      Nonempty (W.model.val.val ≅ G.val) ∧
        ∀ σ, ω σ = outerHom E (transportedAut F Fsep i σ) := by
  let H : SchemeModels Fsep P₀.pair.G := ⟨G, ⟨f⟩⟩
  obtain ⟨C⟩ := relativeFormClassification (S := Fsep) P₀.pair.G
  have hc := Descent.QuasiSplitInnerForms.splitCoefficientMaps (S := Fsep) E
  obtain ⟨c, hci, hcclass⟩ := C.computes H i
  let ω := mapCocycle (outerHom (S := Fsep) E) continuous_of_discreteTopology hc.1 c
  obtain ⟨W⟩ := pinnedRepresentatives E ω
  have hout : mapH1 (outerHom (S := Fsep) E) continuous_of_discreteTopology hc.1
      (C.equiv (Quotient.mk _ H)) = classOf ω := by
    rw [hcclass]
    rfl
  have hH := quasiSplitUniqueness relativeFormClassification
    Descent.BorelInnerAlignment.borelInnerAlignment E C hc ω W H hG hout
  have hW := pinnedClass E C hc ω W
  exact ⟨ω, W, Quotient.exact (C.equiv.injective (hW.trans hH.symm)),
    fun σ => congrArg (outerHom E) (hci σ)⟩

private theorem cocharacterOfOppositeExtension {G : GroupScheme F}
    (c : Cocharacter G) :
    oppositeCocharacter (extendCocharacter (AlgebraicClosure F) c) =
      extendCocharacter (AlgebraicClosure F) (oppositeCocharacter c) :=
  opposite_baseChange c _ (multiplicativeBaseChange_unit (AlgebraicClosure F))

private theorem oppositeLimitBaseChange
    (T : ClosedSubgroup G.val) (c : Cocharacter T.group) :
    oppositeCocharacter (extendCocharacter (AlgebraicClosure F) c) ≫
        (extendSubgroup (AlgebraicClosure F) T).inclusion =
      extendCocharacter (AlgebraicClosure F) (oppositeCocharacter (c ≫ T.inclusion)) := by
  let L := AlgebraicClosure F
  let C := groupBaseChange F L
  have h : extendCocharacter L (c ≫ T.inclusion) =
      extendCocharacter L c ≫ (extendSubgroup L T).inclusion :=
    (congrArg ((multiplicativeBaseChange F L).hom ≫ ·) (C.map_comp c T.inclusion)).trans
      (Category.assoc _ _ _).symm
  calc
    _ = oppositeCocharacter (extendCocharacter L c ≫ (extendSubgroup L T).inclusion) :=
      Category.assoc _ _ _
    _ = oppositeCocharacter (extendCocharacter L (c ≫ T.inclusion)) :=
      congrArg oppositeCocharacter h.symm
    _ = _ := cocharacterOfOppositeExtension (c ≫ T.inclusion)

private theorem limitParabolicBaseChange {K : Type u} [Field K] [Algebra F K]
    {c : Cocharacter G.val} (D : LimitDecomposition c)
    {d : Cocharacter (baseChangedAlgebraicGroup K G).val} (E : LimitDecomposition d)
    (he : d = extendCocharacter K c) :
    SameSubgroup E.parabolic (extendSubgroup K D.parabolic) := by
  subst d
  exact (limits_subgroups_extend G D (multiplicativeBaseChange F K)
    (multiplicativeBaseChange_unit K) E).1

set_option maxHeartbeats 240000 in
private theorem regularOppositeLimitIsBorel
    (hG : IsReductive G) (T : ClosedSubgroup G.val) (c : Cocharacter T.group)
    (hs : GeometricRadicals.IsSplitTorus (extendSubgroup (AlgebraicClosure F) T).group)
    (hTK : IsGeometricallyMaximal (extendSubgroup (AlgebraicClosure F) T))
    (hc : Specs.BorelsAndChambers.IsRegular (extendSubgroup (AlgebraicClosure F) T)
      (extendCocharacter (AlgebraicClosure F) c))
    (E : LimitDecomposition (oppositeCocharacter (c ≫ T.inclusion))) :
    IsKBorel E.parabolic := by
  let L := AlgebraicClosure F
  let TK := extendSubgroup L T
  let cK := extendCocharacter L c
  let J : AffineAlgebraicGroup L := GeometricGroup G
  obtain ⟨EK⟩ := existsLimitDecomposition J (oppositeCocharacter cK ≫ TK.inclusion)
  have hreg : Specs.BorelsAndChambers.IsRegular TK (oppositeCocharacter cK) :=
    @opposite_regular L _ J TK cK hc
  have hEK : IsKBorel EK.parabolic :=
    (regularCocharacterBorel J (reductive_geometricGroup G hG) TK hs hTK _ hreg EK).2.1
  have hEN : SameSubgroup EK.parabolic (extendSubgroup L E.parabolic) :=
    limitParabolicBaseChange E EK (oppositeLimitBaseChange T c)
  refine ⟨(extendSubgroup L E.parabolic).isClosedImmersion, ?_⟩
  change GeometricBorelConjugacy.IsBorel (G := J.val) (extendSubgroup L E.parabolic)
  exact borel_of_same (H := J) ((isKBorel_iff_of_isAlgClosed J EK.parabolic).mp hEK) hEN

set_option maxHeartbeats 300000 in
/-- The cocharacter defining the positive Borel is regular over an
algebraic closure. Its inverse then defines the opposite rational Borel. -/
private theorem rationalOppositeBorel (hG : IsReductive G) (T B : ClosedSubgroup G.val)
    (hB : IsKBorel B) (hT : IsTorus T.group) (hTm : IsGeometricallyMaximal T)
    (hTB : IsSubgroupOf T B) :
    ∃ M : BorelPair G, M.positive = B ∧ M.torus = T := by
  obtain ⟨c, D, hBD, hC⟩ := borelDefiningCocharacter G hG B T hB hT hTm hTB
  obtain ⟨E⟩ := existsLimitDecomposition G (oppositeCocharacter (c ≫ T.inclusion))
  have hCT : SameSubgroup E.centralizer T :=
    sameSubgroupOfCentralizer _ E.centralizer_points
      (fun Y g => (centralizes_opposite_iff _ g).trans (hC Y g))
  have hTE : IsSubgroupOf T E.parabolic := by
    obtain ⟨t, ht⟩ := hCT.2
    exact ⟨t ≫ E.sectionMap, by rw [Category.assoc, E.section_in_G, ht]⟩
  let L := AlgebraicClosure F
  have hs : GeometricRadicals.IsSplitTorus (extendSubgroup L T).group :=
    split_of_maximal (A := GeometricGroup G) hTm.choose_spec
  obtain ⟨hTK, hc, _⟩ := regularAtSplittingField (K := L) G hG T B c D hBD hC hs
  have hN : IsKBorel E.parabolic := regularOppositeLimitIsBorel hG T c hs hTK hc E
  obtain ⟨t, ht⟩ := hTB
  obtain ⟨s, hs'⟩ := hTE
  obtain ⟨U, _, hU, _, _⟩ := borelRadicalAndQuotient hG T B hTm hB t ht
  obtain ⟨V, _, hV, _, _⟩ := borelRadicalAndQuotient hG T E.parabolic hTm hN s hs'
  exact ⟨⟨B, E.parabolic, T, U, V, hB, hN, hT, hTm,
    limitBorelIntersection G T B D E hBD hCT ⟨t, ht⟩ ⟨s, hs'⟩, hU, hV⟩, rfl, rfl⟩

section AdditiveCoordinates

open private additiveLinePointsIso from LinearAlgebraicGroups.RootData.RootGroups
open private additiveParameterBaseChange from LinearAlgebraicGroups.Classification.RationalRealization

variable {K : Type u} [Field K] [Algebra F K]

private theorem additiveBaseChange (A₀ : AdditiveLine F) (A : AdditiveLine K) :
    ∃ e : (groupBaseChange F K).obj A₀.group ≅ A.group,
      ∀ (R : TestAlgebra K) (v : R),
        baseChangePoint F K A₀.group.X R (rootPoint e.inv R v) =
          rootPoint (𝟙 A₀.group) ((restrictTestAlgebra F K).obj R) v := by
  refine additiveParameterBaseChange A₀ A (additiveLinePointsIso A₀).symm
    (additiveLinePointsIso A).symm ?_ ?_
  · intro R v
    exact GrpCat.inv_hom_apply ((additiveLinePointsIso A₀).app R) (Multiplicative.ofAdd v)
  · intro R v
    exact GrpCat.inv_hom_apply ((additiveLinePointsIso A).app R) (Multiplicative.ofAdd v)

end AdditiveCoordinates

section MarkedPair

open Specs.AdjointBorelCohomology (PinnedTwist)
open Specs.QuasiSplitPinnedPairModel (IsBasedLift)
open private scalarExtensionComparison scalarExtensionComparison_comm
  matches_scalarExtensionComparison compareMarkedBorelPairs
  from LinearAlgebraicGroups.Arithmetic.QuasiSplitPinnedPairModel
open private splitTorus_baseChange from LinearAlgebraicGroups.RootData.BorelsAndChambers

variable {K : Type u} [Field K] [Algebra F K]

set_option maxHeartbeats 900000 in
private theorem markedPairOfTwist
    (hG : IsReductive G) (M : BorelPair G)
    (d : PinnedTwist K D₀ l M.positive M.torus) :
    ∃ (N : BorelPair P₀.pair.G) (e : MarkedComparison (K := K) N M),
      N.torus = P₀.pair.T ∧ N.positive = P₀.pair.B ∧
      GeometricRadicals.IsSplitTorus ((groupBaseChange F K).obj M.torus.group) ∧
      MatchesCoordinateComparison e d.groupIso := by
  obtain ⟨N, hB, hT⟩ := QuasiSplitPinnedPairModel.splitOppositePair P₀
  let C := groupBaseChange F K
  let e := scalarExtensionComparison P₀.pair.G G d.groupIso
  have hb : ∃ b : C.obj N.positive.group ≅ C.obj M.positive.group,
      C.map N.positive.inclusion ≫ e.hom = b.hom ≫ C.map M.positive.inclusion := by
    rw [hB]
    let X := closedSubgroupAlgebraicGroup P₀.pair.B
    let Y := closedSubgroupAlgebraicGroup M.positive
    exact ⟨scalarExtensionComparison X Y d.borelIso, scalarExtensionComparison_comm
      (X := X) (Y := Y) P₀.pair.B.inclusion M.positive.inclusion d.groupIso d.borelIso d.borelComm⟩
  have ht : ∃ t : C.obj N.torus.group ≅ C.obj M.torus.group,
      C.map N.torus.inclusion ≫ e.hom = t.hom ≫ C.map M.torus.inclusion := by
    rw [hT]
    let X := closedSubgroupAlgebraicGroup P₀.pair.T
    let Y := closedSubgroupAlgebraicGroup M.torus
    exact ⟨scalarExtensionComparison X Y d.torusIso, scalarExtensionComparison_comm
      (X := X) (Y := Y) P₀.pair.T.inclusion M.torus.inclusion d.groupIso d.torusIso d.torusComm⟩
  obtain ⟨b, hb⟩ := hb
  obtain ⟨t, ht⟩ := ht
  have hs : GeometricRadicals.IsSplitTorus (C.obj N.torus.group) := by
    rw [hT]
    exact splitTorus_baseChange P₀.pair.split
  obtain ⟨hM, cmp, hcmp⟩ :=
    compareMarkedBorelPairs N M P₀.pair.reductive hG e b t hb ht hs
  exact ⟨N, cmp, hT, hB, hM, matches_scalarExtensionComparison cmp d.groupIso hcmp⟩

end MarkedPair

section ComparedPinning

open Specs.AdjointRepresentation (GroupPoints)
open Specs.CharacterDescent (Character)
open Specs.CharacterPairing (characterValue pairing)
open Specs.DatumAndWeyl (Identification)
open LinearAlgebraicGroups.Classification.Pinning (inducedBasedIso)
open Specs.QuasiSplitOrbitDerivedRoots (pinnedRootMap)
open Specs.QuasiSplitPinnedPairModel (IsBasedLift)
open Specs.QuasiSplitOrbitLevis
  (MultiplicativeComparison PreservesUnits simpleCorootOfAttachedDatum
    simplePermutation simpleRootsOfAttachedDatum)
open Specs.RootGroups (HasScalarAction)
open Specs.AdjointBorelCohomology (PinnedTwist)
open CocharacterDynamics (cocharacterPoint laurentAlgebra laurentParameter)
open RootData.RootGroups (additivePoints)
open private laurentParameter_zpow from LinearAlgebraicGroups.Reductive.CocharacterLieWeights
open private pointHom bpoint_morphism from LinearAlgebraicGroups.Reductive.CocharacterLimitSubgroups
open private rootPoint_eq rootPoint_comp from LinearAlgebraicGroups.RootData.RootGroups
open private pinnedComparison_torusAction actualDiagramAction
  from LinearAlgebraicGroups.Arithmetic.QuasiSplitLocalGeneration
open private scalarDatum_coweight scalarCocharacter scalarCocharacter_comparison scalarMorphism
  scalarMorphism_comp scalarMorphism_baseChange
  from LinearAlgebraicGroups.Arithmetic.QuasiSplitFixedWeyl
open private basedIso_ext_weight from LinearAlgebraicGroups.Classification.PinnedEquivalence
open private pinsOfBasedIso from LinearAlgebraicGroups.Arithmetic.QuasiSplitOrbitLevis

variable {K : Type u} [Field K] [Algebra F K]

private theorem laurentExponentEq {n m : ℤ}
    (h : (↑(laurentParameter (CommAlgCat.of K K) ^ n) : LaurentPolynomial K) =
      (↑(laurentParameter (CommAlgCat.of K K) ^ m) : LaurentPolynomial K)) : n = m := by
  rw [laurentParameter_zpow, laurentParameter_zpow] at h
  by_contra hn
  have hz := congrArg (fun f : LaurentPolynomial K => f.coeff m) h
  exact (zero_ne_one : (0 : K) ≠ 1)
    (by simpa only [LaurentPolynomial.T_apply, hn, ite_false, ite_true] using hz)

private theorem cocharacterPoint_comp {k : Type u} [Field k] {T H : GroupScheme k}
    (y : Cocharacter T) (q : T ⟶ H) (R : TestAlgebra k) (v : Rˣ) :
    cocharacterPoint (y ≫ q) R v = pointHom q R (cocharacterPoint y R v) := by
  change ((groupPointsFunctor k).map (y ≫ q)).app R (CocharacterDynamics.unitPoint R v) = _
  rw [Functor.map_comp]
  rfl

set_option maxHeartbeats 900000 in
private theorem pairingOfComparedRoot
    {J : AffineAlgebraicGroup K} {T₀ : ClosedSubgroup P₀.pair.G.val}
    {T : ClosedSubgroup J.val} {A : AdditiveLine K}
    (x₀ : A₀.group ⟶ P₀.pair.G.val) (x : A.group ⟶ J.val)
    (χ₀ : Character T₀.group) (χ : Character T.group)
    (y₀ : Cocharacter T₀.group) (y : Cocharacter T.group)
    (g : (groupBaseChange F K).obj P₀.pair.G.val ≅ J.val)
    (t : (groupBaseChange F K).obj T₀.group ≅ T.group)
    (ht : (groupBaseChange F K).map T₀.inclusion ≫ g.hom = t.hom ≫ T.inclusion)
    (a : (groupBaseChange F K).obj A₀.group ≅ A.group)
    (ha : ∀ (R : TestAlgebra K) (v : R),
      baseChangePoint F K A₀.group.X R (rootPoint a.inv R v) =
        rootPoint (𝟙 A₀.group) ((restrictTestAlgebra F K).obj R) v)
    (m : MultiplicativeComparison F K) (hm : PreservesUnits m)
    (hx : x = a.inv ≫ (groupBaseChange F K).map x₀ ≫ g.hom)
    (hy : y = m.hom ≫ (groupBaseChange F K).map y₀ ≫ t.hom)
    (h₀ : HasScalarAction T₀ χ₀ x₀) (h : HasScalarAction T χ x)
    (hinj : Mono x₀.hom.hom) :
    pairing T.group χ y = pairing T₀.group χ₀ y₀ := by
  let R := laurentAlgebra (CommAlgCat.of K K)
  let R₀ := (restrictTestAlgebra F K).obj R
  let v := laurentParameter (CommAlgCat.of K K)
  let C := groupBaseChange F K
  let b := baseChangePointGroupEquiv K P₀.pair.G.val R
  let r := (((groupPointsFunctor K).mapIso g).app R).groupIsoToMulEquiv
  let e : GroupPoints P₀.pair.G.val R₀ ≃* GroupPoints J.val R := b.symm.trans r
  have hTo (z : R) : rootPoint x R z = e (rootPoint x₀ R₀ z) := by
    have hx' : x = (a.inv ≫ C.map x₀) ≫ g.hom := hx.trans (Category.assoc _ _ _).symm
    rw [hx', rootPoint_comp, rootPoint_comp]
    change r (pointHom (C.map x₀) R (rootPoint a.inv R z)) = r (b.symm (rootPoint x₀ R₀ z))
    apply congrArg r
    apply b.injective
    rw [b.apply_symm_apply]
    rw [show b (pointHom (C.map x₀) R (rootPoint a.inv R z)) =
      pointHom x₀ R₀ (baseChangePoint F K A₀.group.X R (rootPoint a.inv R z)) from
      bpoint_morphism x₀ _]
    rw [ha R z]
    change rootPoint (𝟙 A₀.group) R₀ z ≫ x₀.hom.hom = rootPoint x₀ R₀ z
    rw [← rootPoint_comp, Category.id_comp]
  have hTc : pointHom T.inclusion R (cocharacterPoint y R v) =
      e (pointHom T₀.inclusion R₀ (cocharacterPoint y₀ R₀ v)) := by
    have ht' : y ≫ T.inclusion =
        (m.hom ≫ C.map (y₀ ≫ T₀.inclusion)) ≫ g.hom := by
      rw [hy]
      simp only [Category.assoc]
      rw [← ht, ← Category.assoc (C.map y₀), ← C.map_comp]
    rw [← cocharacterPoint_comp y T.inclusion R v, ht',
      cocharacterPoint_comp _ g.hom R v, cocharacterPoint_comp m.hom _ R v]
    change r (pointHom (C.map (y₀ ≫ T₀.inclusion)) R
        (pointHom m.hom R (CocharacterDynamics.unitPoint R v))) =
      r (b.symm (pointHom T₀.inclusion R₀ (cocharacterPoint y₀ R₀ v)))
    apply congrArg r
    apply b.injective
    rw [b.apply_symm_apply]
    rw [show b (pointHom (C.map (y₀ ≫ T₀.inclusion)) R
      (pointHom m.hom R (CocharacterDynamics.unitPoint R v))) =
        pointHom (y₀ ≫ T₀.inclusion) R₀
          (baseChangePoint F K (Specs.Arithmetic.QuasiSplitFixedWeyl.multiplicativeGroup F).X R
            (pointHom m.hom R (CocharacterDynamics.unitPoint R v))) from bpoint_morphism _ _]
    have hm' : baseChangePoint F K (Specs.Arithmetic.QuasiSplitFixedWeyl.multiplicativeGroup F).X R
        (pointHom m.hom R (CocharacterDynamics.unitPoint R v)) =
        CocharacterDynamics.unitPoint R₀ v := hm R v
    rw [hm']
    exact cocharacterPoint_comp y₀ T₀.inclusion R₀ v
  have hu := h R (cocharacterPoint y R v) 1
  have hu₀ := h₀ R₀ (cocharacterPoint y₀ R₀ v) 1
  change pointHom T.inclusion R (cocharacterPoint y R v) * rootPoint x R 1 *
    (pointHom T.inclusion R (cocharacterPoint y R v))⁻¹ =
      rootPoint x R (characterValue χ R (cocharacterPoint y R v) * 1) at hu
  change pointHom T₀.inclusion R₀ (cocharacterPoint y₀ R₀ v) * rootPoint x₀ R₀ 1 *
    (pointHom T₀.inclusion R₀ (cocharacterPoint y₀ R₀ v))⁻¹ =
      rootPoint x₀ R₀ (characterValue χ₀ R₀ (cocharacterPoint y₀ R₀ v) * 1) at hu₀
  rw [hTc, hTo 1, hTo (characterValue χ R (cocharacterPoint y R v) * 1),
    ← map_inv e, ← map_mul e, ← map_mul e, hu₀] at hu
  have he := e.injective hu
  rw [mul_one, mul_one, rootPoint_eq, rootPoint_eq] at he
  letI := hinj
  have hv := (additivePoints A₀ R₀).injective ((cancel_mono x₀.hom.hom).mp he)
  rw [(RootData.CharacterPairing.characterPairingComposition T₀.group χ₀ y₀).2,
    (RootData.CharacterPairing.characterPairingComposition T.group χ y).2] at hv
  exact (laurentExponentEq (K := K) hv).symm

set_option maxHeartbeats 900000 in
private theorem comparedActionOnLabels
    (hl : IsBasedLift D₀ l) {M : BorelPair G} {N : BorelPair P₀.pair.G}
    (d : PinnedTwist K D₀ l M.positive M.torus) (e : MarkedComparison (K := K) N M)
    (he : MatchesCoordinateComparison e d.groupIso)
    (t : (groupBaseChange F K).obj P₀.pair.T.group ≅ (groupBaseChange F K).obj M.torus.group)
    (ht : (groupBaseChange F K).map P₀.pair.T.inclusion ≫ e.groupIso.hom =
      t.hom ≫ (groupBaseChange F K).map M.torus.inclusion)
    (P : SplitPairOver (K := K) G M.torus M.positive)
    (D : AttachedDatum P.pair) (W : letI := D.comm; Identification D.datum)
    (j : D₀.toBased.base.support ≃ D.toBased.base.support)
    (ω : Gal(K/F) →* Aut D.toBased)
    (hω : letI := D.comm; ∀ σ, (ω σ).asIso.hom.val = actualDiagramAction P D W σ)
    (hy : letI := D.comm; letI := D₀.comm
      ∀ i : D₀.toBased.base.support,
        (D.datum.rootDatum.coroot (j i).val).toMul =
          (multiplicativeBaseChange F K).hom ≫
            (groupBaseChange F K).map (D₀.datum.rootDatum.coroot i.val).toMul ≫ t.hom) :
    ∀ σ i, simplePermutation D (ω σ) (j i) = j (simplePermutation D₀ (d.outer σ) i) := by
  letI := D₀.comm
  letI := D.comm
  letI : IsCommMonObj (GeometricRadicals.baseChangedSubgroup K M.torus P.torusClosed).group.X := D.comm
  let C := groupBaseChange F K
  let m := multiplicativeBaseChange F K
  let y₀ (i : D₀.toBased.base.support) := (D₀.datum.rootDatum.coroot i.val).toMul
  let y (i : D₀.toBased.base.support) := (D.datum.rootDatum.coroot (j i).val).toMul
  have hyn (i : D₀.toBased.base.support) : m.inv ≫ y i = C.map (y₀ i) ≫ t.hom := by
    rw [show y i = m.hom ≫ C.map (y₀ i) ≫ t.hom from hy i, Iso.inv_hom_id_assoc]
  intro σ i
  let π := simplePermutation D₀ (d.outer σ)
  let f := (l (d.outer σ)).asIso.hom
  have hf : inducedBasedIso f D₀ D₀ = (d.outer σ).asIso.hom :=
    basedIso_ext_weight _ _ (fun z => ((hl (d.outer σ)).1 z.toMul).symm)
  have hmarks : y₀ i ≫ f.torus.hom = y₀ (π i) :=
    (pinsOfBasedIso f (d.outer σ).asIso.hom hf
      (simpleRootsOfAttachedDatum P₀ D₀ i) (simpleRootsOfAttachedDatum P₀ D₀ (π i)) rfl).2.2
  have hco : scalarCocharacter σ (T := M.torus.group) (y i) = y (π i) := by
    apply (cancel_epi m.inv).mp
    rw [scalarCocharacter_comparison]
    change scalarMorphism σ (m.inv ≫ y i) = m.inv ≫ y (π i)
    rw [hyn, hyn, scalarMorphism_comp, scalarMorphism_baseChange,
      pinnedComparison_torusAction d e he t ht σ, ← Category.assoc, ← C.map_comp, hmarks]
  let r := D.datum.rootDatum
  let δ : r.Aut := actualDiagramAction P D W σ
  have hδ : (ω σ).asIso.hom.val = δ := hω σ
  have hindex : δ.indexEquiv (j i).val = (j (π i)).val := by
    apply r.coroot.injective
    have hc := δ.toHom.coroot_coweightMap_apply r r (δ.indexEquiv (j i).val)
    change δ.coweightEquiv (r.coroot (δ.indexEquiv (j i).val)) =
      r.coroot (δ.indexEquiv.symm (δ.indexEquiv (j i).val)) at hc
    rw [Equiv.symm_apply_apply] at hc
    apply δ.coweightEquiv.injective
    rw [hc]
    have hs : δ.coweightEquiv.symm (Additive.ofMul (y i)) = Additive.ofMul (y (π i)) :=
      (scalarDatum_coweight (G := G) (T := M.torus) (hT := P.torusClosed) W P.split σ
        (y i)).trans (congrArg Additive.ofMul hco)
    exact (δ.coweightEquiv.symm_apply_eq).mp hs
  apply Subtype.ext
  exact (congrArg (fun z : r.Aut => z.indexEquiv (j i).val) hδ).trans hindex

end ComparedPinning

section Construction

open Specs.AdjointBorelCohomology (PinnedTwist)
open Specs.DatumAndWeyl (Identification)
open Specs.Pinning (Pinning)
open Specs.QuasiSplitOrbitDerivedRoots (pinnedRootMap)
open Specs.QuasiSplitOrbitLevis
  (MultiplicativeComparison PreservesUnits simpleCorootOfAttachedDatum
    simplePermutation simpleRootsOfAttachedDatum)
open private exists_weylIdentification
  from LinearAlgebraicGroups.Classification.TransportedRootCoordinates
open private commonTorus_le_borel from LinearAlgebraicGroups.Arithmetic.QuasiSplitPinnedPairModel
open private splitPairAfterExtension splitPinnedCoordinates comparisonOnMark
  comparisonOnMark_commutes ambientPinningAction actualDiagramAction
  from LinearAlgebraicGroups.Arithmetic.QuasiSplitLocalGeneration
open private reparametrizePin reparametrizeRootMap
  from LinearAlgebraicGroups.Arithmetic.QuasiSplitOrbitLevis
open private scalarDatum_isScalarAction
  from LinearAlgebraicGroups.Arithmetic.QuasiSplitFixedWeyl

set_option maxHeartbeats 1600000 in
/-- Construct the labelled finite-layer pinning of the prescribed quasi-split form. -/
theorem pinnedBorelPair : Statement.{u} := by
  intro F Fsep _ _ _ _ G hsem _ hG A₀ P₀ D₀ l Q E f i _
  have hred := reductive_of_semisimple G hsem
  obtain ⟨ω₀, W, ⟨v⟩, hω₀⟩ := pinnedRepresentativeOfTrivialization hG E f i
  let K := W.layer
  let B := transportSubgroup v W.B
  let T := transportSubgroup v W.T
  have hb : IsKBorel B := pushKBorel v W.borel
  have ht : IsTorus T.group := W.torus
  have htmax : IsGeometricallyMaximal T := maximalTransport v W.T W.maximal
  have hTB : IsSubgroupOf T B := by
    refine ⟨W.j, ?_⟩
    change W.j ≫ W.B.inclusion ≫ v.hom = (W.T.inclusion ≫ v.hom)
    rw [← Category.assoc, W.j_comm]
  obtain ⟨M, hMB, hMT⟩ := rationalOppositeBorel hred T B hb ht htmax hTB
  have hTw : ∃ d : PinnedTwist K D₀ l M.positive M.torus, d.outer = W.data.outer := by
    rw [hMB, hMT]
    exact ⟨transportPinnedTwist W.data v (Iso.refl _) (Iso.refl _)
      (Category.id_comp _).symm (Category.id_comp _).symm, rfl⟩
  obtain ⟨d, hd⟩ := hTw
  have hTM := commonTorus_le_borel M (B := M.positive) (by simp)
  obtain ⟨S, hS, hmax, hcentral, hmin, hcontains⟩ :=
    QuasiSplitFixedWeyl.quasiSplitCentralizer G hred M.positive M.torus
      M.positiveBorel M.isTorus M.maximal hTM
  obtain ⟨N, e, hNT, hNB, hsplit, hcomp⟩ := markedPairOfTwist hred M d
  obtain ⟨P⟩ := splitPairAfterExtension M hred hsplit
  let C := groupBaseChange F K
  let m := multiplicativeBaseChange F K
  have hm : PreservesUnits m := fun R v => multiplicativeBaseChange_unit K R v
  let tk := comparisonOnMark e .torus hNT
  let bk := comparisonOnMark e .positive hNB
  have htk := comparisonOnMark_commutes e .torus hNT
  have hbk := comparisonOnMark_commutes e .positive hNB
  obtain ⟨A, U, p₀, D, a₀, j, hx₀, hy⟩ :=
    splitPinnedCoordinates P₀ D₀ P.pair e.groupIso tk bk htk hbk m hm
  letI := D₀.comm
  letI := D.comm
  letI : IsCommMonObj (GeometricRadicals.baseChangedSubgroup K M.torus P.torusClosed).group.X := D.comm
  obtain ⟨a, ha⟩ := additiveBaseChange A₀ A
  let p := (reparametrizePin (⟨P.pair, U, p₀⟩ : PinnedGroup A) (a.symm ≪≫ a₀)).pin
  let J : PinnedGroup A := ⟨P.pair, U, p⟩
  have hx (i : D₀.toBased.base.support) :
      pinnedRootMap p (simpleRootsOfAttachedDatum J D (j i)) =
        a.inv ≫ C.map (pinnedRootMap P₀.pin (simpleRootsOfAttachedDatum P₀ D₀ i)) ≫ e.groupIso.hom := by
    change pinnedRootMap (reparametrizePin (⟨P.pair, U, p₀⟩ : PinnedGroup A) (a.symm ≪≫ a₀)).pin _ = _
    rw [reparametrizeRootMap]
    change (a.inv ≫ a₀.hom) ≫
      pinnedRootMap p₀ (simpleRootsOfAttachedDatum (⟨P.pair, U, p₀⟩ : PinnedGroup A) D (j i)) = _
    rw [hx₀, Category.assoc, a₀.hom_inv_id_assoc]
  obtain ⟨H⟩ := exists_weylIdentification P.pair D
  have hl := basedLift_of_splitSequence E
  obtain ⟨ω, hpin, hω⟩ := ambientPinningAction D₀ l hl d e hcomp tk htk P U p D H a j hx hy
  have hact : underlyingAction D ω = actualDiagramAction P D H :=
    DFunLike.ext _ _ hω
  have hs : Specs.Arithmetic.QuasiSplitFixedWeyl.IsScalarAction M.torus P.torusClosed
      D.comm D.datum m (underlyingAction D ω) := by
    rw [hact]
    exact scalarDatum_isScalarAction (G := G) (T := M.torus) (hT := P.torusClosed) H P.split
  refine ⟨K, M, S, hS, hmax, hcentral, hmin, hcontains, P, D, H, A, U, p, a, m, ω, j,
    ha, hm, hpin, hs, ?_, ?_⟩
  · intro x y
    let α₀ := simpleRootsOfAttachedDatum P₀ D₀ y
    let α := simpleRootsOfAttachedDatum J D (j y)
    let c₀ := simpleCorootOfAttachedDatum P₀ D₀ (simpleRootsOfAttachedDatum P₀ D₀ x)
    let c := simpleCorootOfAttachedDatum J D (simpleRootsOfAttachedDatum J D (j x))
    change D.datum.rootDatum.pairing α.val
      (simpleRootsOfAttachedDatum J D (j x)).val =
      D₀.datum.rootDatum.pairing α₀.val (simpleRootsOfAttachedDatum P₀ D₀ x).val
    rw [← RootPairing.root_coroot_eq_pairing, ← RootPairing.root_coroot_eq_pairing,
      D.datum.root_eq, D₀.datum.root_eq]
    change D.datum.rootDatum.toLinearMap (Additive.ofMul α.val.val) (Additive.ofMul c) =
      D₀.datum.rootDatum.toLinearMap (Additive.ofMul α₀.val.val) (Additive.ofMul c₀)
    rw [D.datum.pairing_eq, D₀.datum.pairing_eq]
    have hmono : Mono (pinnedRootMap P₀.pin α₀).hom.hom := by
      let I := Grp.forget (SchemeOver F)
      letI := I.map_isIso (P₀.pin α₀).val.hom
      let V := (P₀.roots α₀.val).val
      letI := V.isClosedImmersion
      letI : Mono V.inclusion.hom.hom := Over.mono_of_mono_left _
      change Mono ((P₀.pin α₀).val.hom.hom.hom ≫ V.inclusion.hom.hom)
      infer_instance
    exact pairingOfComparedRoot (pinnedRootMap P₀.pin α₀) (pinnedRootMap p α)
      α₀.val.val α.val.val c₀ c e.groupIso tk htk a ha m hm (hx y) (hy x)
      (P₀.pin α₀).property (p α).property hmono
  · have hlabels := comparedActionOnLabels hl d e hcomp tk htk P D H j ω hω hy
    intro σ x
    rw [hlabels, hd, W.outer_eq, hω₀]

end Construction

end

end LinearAlgebraicGroups.Arithmetic.TrialitarianPinnedBorelPair
