import Specs.LinearAlgebraicGroups.Relative.ParabolicIntersection
import LinearAlgebraicGroups.Affine.SchemeImageQuotient
import LinearAlgebraicGroups.Flag.BruhatCells
import LinearAlgebraicGroups.Flag.StandardParabolics
import LinearAlgebraicGroups.Relative.RationalCocharacter
import Batteries.Tactic.OpenPrivate
import Mathlib.Tactic.Group

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

universe u

namespace LinearAlgebraicGroups.Relative.ParabolicIntersection

open _root_.LinearAlgebraicGroups.Specs
open Specs.ParabolicIntersection
open Specs.RationalCocharacter
open Specs.BorelProper (IsParabolic)
open Specs.CharacterDescent (Cocharacter)
open Specs.GeometricBorelConjugacy (IsBorel ConjugatesSubgroups subgroupOfSubgroup)
open Specs.GeometricRadicals (GeometricGroup IsReductive IsMaximalTorus IsTorus IsUnipotentRadical)
open Specs.RankOneFlag (SameSubgroup)
open Specs.SchemeDerivedGroup (IsSubgroupOf FactorsThrough)
open Specs.StandardParabolicLevi (IsContractingRadical)
open Specs.SubtorusCentralizer (IsCentralizer)
open Specs.BorelsAndChambers (contractingSubgroup)
open Specs.Unipotent (closedSubgroupAlgebraicGroup)
open Specs.UnipotentRadicalIntersection (IsSchemeIntersection)
open Specs.AdjointRepresentation (GroupPoints)
open LinearAlgebraicGroups.CocharacterDynamics
open LinearAlgebraicGroups.Relative.RationalCocharacter
  (rationalParabolic rationalParabolicThroughTorus)

open private subgroupOf_mutual_iso factor_group_through_subgroup
  from LinearAlgebraicGroups.Reductive.GeometricBorelConjugacy
open private inclusion_mono conjugationIso conjugate comp_conjugate conjugates_trans conjugates_maximal
  conjugate_comp conjugates_preserves_borel transportSubgroup restrictSubgroup compose_restrict
  local_maximal_of_ambient
  from LinearAlgebraicGroups.Reductive.MaximalToriConjugate
open private maximal_torus_in_borel reductive_geometric connected_of_reductive
  isKBorel_iff_of_isAlgClosed split_of_maximal geometricMaximal_of_maximal
  conjugates_transport_ambient conjugates_same_target conjugates_of_normalizes
  normalizes_inv extendSubgroup smooth_extend_iff
  factor_laurent_descends
  from LinearAlgebraicGroups.RootData.BorelNormalizer
open private subgroup_of_intersection sections_of_subgroup
  from LinearAlgebraicGroups.Reductive.UnipotentRadicalIntersection
open private lift_of_range from LinearAlgebraicGroups.Flag.BruhatCells
open private map_limit_parabolic from LinearAlgebraicGroups.RootData.RankOneFlag
open private subgroupInclusionFactors pointHom
  from LinearAlgebraicGroups.Reductive.CocharacterLimitSubgroups
open private fieldSpecMap_surjective from LinearAlgebraicGroups.Affine.Stabilizers
open private baseChangeMapPullback baseChangeKernelSquare from LinearAlgebraicGroups.Affine.Components
open private pushSubgroup radical_transport from LinearAlgebraicGroups.RootData.OrderedRootProducts
open private baseChanged_radical_transport transportedLimitKernel
  from LinearAlgebraicGroups.RootData.BorelPositivity
open private lattice_torus_of_split from LinearAlgebraicGroups.RootData.RankOneFlag
open private schemeKernel_sections from LinearAlgebraicGroups.Affine.SchemeImageQuotient
open private reduced_of_flat_local_cover from LinearAlgebraicGroups.Reductive.SubtorusCentralizer
open private isReduced_of_smooth_over_field from LinearAlgebraicGroups.Affine.SmoothnessCriteria

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000

variable {k : Type u} [Field k] {G : GroupScheme k}

private theorem subgroupTrans {A B C : ClosedSubgroup G}
    (hAB : IsSubgroupOf A B) (hBC : IsSubgroupOf B C) : IsSubgroupOf A C := by
  obtain ⟨f, hf⟩ := hAB
  obtain ⟨g, hg⟩ := hBC
  exact ⟨f ≫ g, by rw [Category.assoc, hg, hf]⟩

private theorem transportSubgroup_le {A B B' : ClosedSubgroup G}
    {g : 𝟙_ (SchemeOver k) ⟶ G.X} (h : IsSubgroupOf A B)
    (hc : ConjugatesSubgroups g B B') :
    IsSubgroupOf (transportSubgroup (conjugationIso g) A) B' := by
  obtain ⟨j, hj⟩ := h
  obtain ⟨e, he⟩ := hc
  have he' : e.hom ≫ B'.inclusion = B.inclusion ≫ (conjugationIso g).hom := by
    apply Grp.hom_ext
    change (e.hom ≫ B'.inclusion).hom.hom = B.inclusion.hom.hom ≫ conjugate g (𝟙 G.X)
    rw [comp_conjugate, Category.comp_id]
    exact he
  exact ⟨j ≫ e.hom, by
    change (j ≫ e.hom) ≫ B'.inclusion = A.inclusion ≫ (conjugationIso g).hom
    rw [Category.assoc, he', ← Category.assoc, hj]⟩

private theorem rationalBruhat [IsAlgClosed k] (A : AffineAlgebraicGroup k)
    (hA : IsReductive A) {T B : ClosedSubgroup A.val}
    (hT : IsMaximalTorus T) (hB : IsBorel B) (hTB : IsSubgroupOf T B)
    (g : 𝟙_ (SchemeOver k) ⟶ A.val.X) :
    ∃ (n : 𝟙_ (SchemeOver k) ⟶ A.val.X)
      (b₁ b₂ : 𝟙_ (SchemeOver k) ⟶ B.group.X),
      Normalizes T.inclusion n ∧
        (b₁ ≫ B.inclusion.hom.hom) * n * (b₂ ≫ B.inclusion.hom.hom) = g := by
  classical
  obtain ⟨hc, D, I, U, Bneg, Rpos, Rneg, c, b, _, _, _, _, _, _, _, _, hn, ⟨Q⟩, hcells⟩ :=
    LinearAlgebraicGroups.Flag.BruhatCells.bruhatCells A hA T B (split_of_maximal hT)
      (geometricMaximal_of_maximal A T hT) ((isKBorel_iff_of_isAlgClosed A B).mpr hB) hTB
  letI := hc
  choose n hn' using hn
  obtain ⟨a, _, cells⟩ := hcells Q
  obtain ⟨J, C, _, _, hcover, _⟩ := cells n hn'
  have hx : g.left (IsLocalRing.closedPoint k) ∈ ⋃ w, Set.range (C w).doubleOrbitInclusion.left :=
    hcover.symm ▸ Set.mem_univ _
  obtain ⟨w, hw⟩ := Set.mem_iUnion.mp hx
  let S := Over.mk (fieldSpecMap k k)
  have hs : IsTerminal S := by
    change IsTerminal (Over.mk (fieldSpecMap k k))
    have hself : fieldSpecMap k k = 𝟙 _ := by simp [fieldSpecMap]
    rw [hself]
    exact Over.mkIdTerminal
  let e := hs.uniqueUpToIso (isTerminalTensorUnit (C := SchemeOver k))
  let f := (C w).doubleOrbitInclusion
  letI : LocallyOfFiniteType f.left := by
    letI := (C w).doubleOrbitImmersion
    infer_instance
  have he : e.hom.left = 𝟙 _ := by
    change e.hom.left = 𝟙 (Spec (CommRingCat.of k))
    simpa [S, fieldSpecMap] using Over.w e.hom
  have hpoint : (e.hom ≫ g).left (IsLocalRing.closedPoint k) ∈ Set.range f.left := by
    change (e.hom.left ≫ g.left) (IsLocalRing.closedPoint k) ∈ _
    rwa [he, Category.id_comp]
  obtain ⟨x, hx⟩ := lift_of_range f (e.hom ≫ g) hpoint
  obtain ⟨b₁, b₂, hb⟩ := ((C w).doubleOrbitSections _ g).mp
    ⟨e.inv ≫ x, by rw [Category.assoc, hx, e.inv_hom_id_assoc]⟩
  refine ⟨n w ≫ I.normalizer.inclusion.hom.hom, b₁, b₂,
    (I.representsNormalizer _ _).mpr ⟨n w, rfl⟩, ?_⟩
  have hu : toUnit (𝟙_ (SchemeOver k)) = 𝟙 _ := Subsingleton.elim _ _
  simpa only [hu, Category.id_comp] using hb

private theorem commonTorusInBorels [IsAlgClosed k] (A : AffineAlgebraicGroup k)
    (hA : IsReductive A) {B C : ClosedSubgroup A.val} (hB : IsBorel B) (hC : IsBorel C) :
    ∃ T : ClosedSubgroup A.val, IsMaximalTorus T ∧ IsSubgroupOf T B ∧ IsSubgroupOf T C := by
  obtain ⟨S, _, hT⟩ := maximal_torus_in_borel A hA B hB
  let T := subgroupOfSubgroup B S
  have hTB : IsSubgroupOf T B := ⟨S.inclusion, rfl⟩
  obtain ⟨g, hg⟩ := LinearAlgebraicGroups.GeometricBorelConjugacy.borelsConjugate
    A hA.1 (connected_of_reductive A hA) B C hB hC
  obtain ⟨n, b₁, b₂, hn, hprod⟩ := rationalBruhat A hA hT hB hTB g
  let a := b₁ ≫ B.inclusion.hom.hom
  let b := b₂ ≫ B.inclusion.hom.hom
  let T' := transportSubgroup (conjugationIso a) T
  have hT' := conjugates_transport_ambient T a
  refine ⟨T', conjugates_maximal hT' hT,
    transportSubgroup_le hTB (conjugates_preserves_borel B b₁), ?_⟩
  let S' := transportSubgroup (conjugationIso (b⁻¹)) T
  have hS' := conjugates_transport_ambient T (b⁻¹)
  have hSB : IsSubgroupOf S' B := by
    have hb : b⁻¹ = b₂⁻¹ ≫ B.inclusion.hom.hom := by simp only [b, GrpObj.inv_comp]
    have hc : ConjugatesSubgroups (b⁻¹) B B := hb.symm ▸ conjugates_preserves_borel B b₂⁻¹
    exact transportSubgroup_le hTB hc
  have hnorm := conjugates_of_normalizes T (normalizes_inv T hn)
  have h := conjugates_trans (conjugates_trans hnorm hS') (conjugates_transport_ambient S' g)
  have hh : g * (b⁻¹ * n⁻¹) = a := by
    change a * n * b = g at hprod
    rw [← hprod]
    group
  rw [hh] at h
  exact subgroupTrans (conjugates_same_target hT' h).1 (transportSubgroup_le hSB hg)

/-- The intersection of two closed subgroups by the pullback in group schemes. -/
private def intersection (P Q : ClosedSubgroup G) : ClosedSubgroup G := by
  let a := pullback.fst P.inclusion Q.inclusion
  have square := ((Grp.forget (SchemeOver k) ⋙ Over.forget _)).map_isPullback
    (IsPullback.of_hasPullback P.inclusion Q.inclusion)
  haveI : IsClosedImmersion a.hom.hom.left :=
    MorphismProperty.of_isPullback square.flip Q.isClosedImmersion
  letI := P.isClosedImmersion
  exact ⟨_, a ≫ P.inclusion, IsClosedImmersion.comp a.hom.hom.left P.inclusion.hom.hom.left⟩

private theorem intersection_spec {I : ClosedSubgroup G} {P Q : ClosedSubgroup G}
    {a : I.group ⟶ P.group} {b : I.group ⟶ Q.group}
    (h : IsPullback a b P.inclusion Q.inclusion) (ha : a ≫ P.inclusion = I.inclusion) :
    IsSchemeIntersection {P, Q} I := by
  have h' : IsPullback a.hom.hom b.hom.hom P.inclusion.hom.hom Q.inclusion.hom.hom :=
    (Grp.forget (SchemeOver k)).map_isPullback h
  have ha' : a.hom.hom ≫ P.inclusion.hom.hom = I.inclusion.hom.hom :=
    congrArg (fun f : I.group ⟶ G ↦ f.hom.hom) ha
  have hb' : b.hom.hom ≫ Q.inclusion.hom.hom = I.inclusion.hom.hom :=
    h'.w.symm.trans ha'
  intro Y y
  constructor
  · rintro ⟨z, hz⟩ B hB
    change z ≫ I.inclusion.hom.hom = y at hz
    have hcases : B = P ∨ B = Q := by simpa using hB
    rcases hcases with hBP | hBQ
    · rw [hBP]
      refine ⟨z ≫ a.hom.hom, ?_⟩
      change (z ≫ a.hom.hom) ≫ P.inclusion.hom.hom = y
      rw [Category.assoc, ha', hz]
    · rw [hBQ]
      refine ⟨z ≫ b.hom.hom, ?_⟩
      change (z ≫ b.hom.hom) ≫ Q.inclusion.hom.hom = y
      rw [Category.assoc, hb', hz]
  · intro hy
    obtain ⟨p, hp⟩ := hy P (by simp)
    obtain ⟨q, hq⟩ := hy Q (by simp)
    change p ≫ P.inclusion.hom.hom = y at hp
    change q ≫ Q.inclusion.hom.hom = y at hq
    have eq := hp.trans hq.symm
    refine ⟨h'.lift p q eq, ?_⟩
    change h'.lift p q eq ≫ I.inclusion.hom.hom = y
    rw [← ha', ← Category.assoc, h'.lift_fst]
    exact hp

private theorem pullbackIntersection (P Q : ClosedSubgroup G) :
    IsSchemeIntersection {P, Q} (intersection P Q) :=
  intersection_spec (IsPullback.of_hasPullback P.inclusion Q.inclusion) rfl

private theorem baseChangedIntersection (K : Type u) [Field K] [Algebra k K]
    (P Q : ClosedSubgroup G) :
    IsSchemeIntersection {extendSubgroup K P, extendSubgroup K Q}
      (extendSubgroup K (intersection P Q)) := by
  apply intersection_spec (LinearAlgebraicGroups.baseChangeSubgroupPullback k K
    (IsPullback.of_hasPullback P.inclusion Q.inclusion))
  exact (groupBaseChange k K).map_comp _ _ |>.symm

private theorem parabolicOverClosedField [IsAlgClosed k] (A : AffineAlgebraicGroup k)
    (hA : IsReductive A) (P : ClosedSubgroup A.val)
    (hP : Smooth P.group.X.hom) {B : ClosedSubgroup A.val}
    (hB : IsBorel B) (hBP : IsSubgroupOf B P) : IsParabolic A P := by
  obtain ⟨hBc, hBc'⟩ := (isKBorel_iff_of_isAlgClosed A B).mpr hB
  refine ⟨hA, hP, (extendSubgroup (AlgebraicClosure k) P).isClosedImmersion,
    Specs.GeometricRadicals.baseChangedSubgroup (AlgebraicClosure k) B hBc, hBc', ?_⟩
  obtain ⟨i, hi⟩ := hBP
  exact ⟨(groupBaseChange k (AlgebraicClosure k)).map i, by
    change _ ≫ (groupBaseChange k (AlgebraicClosure k)).map P.inclusion = _
    rw [← Functor.map_comp, hi]
    rfl⟩

private theorem geometricParabolic (A : AffineAlgebraicGroup k)
    {P : ClosedSubgroup A.val} (hP : IsParabolic A P) :
    IsParabolic (GeometricGroup A) (extendSubgroup (AlgebraicClosure k) P) := by
  obtain ⟨_, B, hB, hBP⟩ := hP.2.2
  exact parabolicOverClosedField _ (reductive_geometric A hP.1) _
    ((smooth_extend_iff (AlgebraicClosure k) P.group.X).mpr hP.2.1) hB hBP

private theorem commonGeometricTorus (A : AffineAlgebraicGroup k)
    {P Q : ClosedSubgroup A.val} (hP : IsParabolic A P) (hQ : IsParabolic A Q) :
    CommonGeometricMaximalTorus P Q := by
  obtain ⟨hp, B, hB, hBP⟩ := hP.2.2
  obtain ⟨hq, C, hC, hCQ⟩ := hQ.2.2
  obtain ⟨T, hT, hTB, hTC⟩ := commonTorusInBorels (GeometricGroup A)
    (reductive_geometric A hP.1) hB hC
  exact ⟨hp, hq, T, hT, subgroupTrans hTB hBP, subgroupTrans hTC hCQ⟩

private theorem subgroupGeometryOfIso {A B : GroupScheme k} (e : A ≅ B)
    (hs : Smooth B.X.hom) (hc : GeometricallyConnected B.X.hom) :
    Smooth A.X.hom ∧ GeometricallyConnected A.X.hom := by
  letI : IsIso e.hom.hom.hom.left :=
    (Grp.forget (SchemeOver k) ⋙ Over.forget _).map_isIso e.hom
  have hcIso : GeometricallyConnected e.hom.hom.hom.left := by
    constructor
    apply (geometrically_iff_of_isClosedUnderIsomorphisms
      (P := fun Z : Scheme.{u} ↦ ConnectedSpace Z)).mpr
    intro K _ y
    let f := pullback.snd e.hom.hom.hom.left y
    letI : IsIso f := inferInstanceAs (IsIso (pullback.snd e.hom.hom.hom.left y))
    exact f.homeomorph.connectedSpace_iff.mpr inferInstance
  letI := hs
  letI := hc
  letI := hcIso
  rw [← Over.w e.hom.hom.hom]
  exact ⟨inferInstance, GeometricallyConnected.comp _ _⟩

private theorem parabolicConnected (rational : RationalParabolic.{u})
    (A : AffineAlgebraicGroup k) (P : ClosedSubgroup A.val) (hP : IsParabolic A P) :
    ConnectedSpace P.group.X.left := by
  obtain ⟨c, D, hsame, _, _⟩ := rational A P hP
  obtain ⟨e, _⟩ := subgroupOf_mutual_iso hsame.1 hsame.2
  letI := hP.1.1
  letI := connected_of_reductive A hP.1
  have hc := (geometricallyConnectedLimitSubgroups A c D).1
  letI := (subgroupGeometryOfIso e (limitSubgroupsSmooth A c D).1 hc).2
  exact GeometricallyConnected.connectedSpace_of_subsingleton P.group.X.hom

private theorem orbitThroughSubgroup {S : ClosedSubgroup G} (c : Cocharacter S.group)
    {R : TestAlgebra k} (g : GroupPoints S.group R) :
    orbit (c ≫ S.inclusion) (show GroupPoints G R from g ≫ S.inclusion.hom.hom) =
      orbit c g ≫ S.inclusion.hom.hom := by
  symm
  change (_ * _ * _) ≫ S.inclusion.hom.hom = _ * _ * _
  rw [MonObj.mul_comp, MonObj.mul_comp, GrpObj.inv_comp]
  simp only [cocharacterPoint, Category.assoc]
  rfl

/-- A polynomial limit in the ambient group of an orbit in a closed subgroup
lifts to the closed subgroup, including its value at zero. -/
private theorem restrictLimit (A : AffineAlgebraicGroup k) (S : ClosedSubgroup A.val)
    (c : Cocharacter S.group) {R : TestAlgebra k} (g : GroupPoints S.group R)
    (z : GroupPoints A.val R)
    (h : HasLimit (c ≫ S.inclusion) (g ≫ S.inclusion.hom.hom) z) :
    ∃ zS : GroupPoints S.group R, HasLimit c g zS ∧ zS ≫ S.inclusion.hom.hom = z := by
  obtain ⟨f, hf, hz⟩ := h
  have hmem : FactorsThrough S (mapPoints (polynomialToLaurent R) f) :=
    ⟨orbit c g, (orbitThroughSubgroup c g).symm.trans hf.symm⟩
  obtain ⟨p, hp⟩ := factor_laurent_descends A S R f hmem
  change p ≫ S.inclusion.hom.hom = f at hp
  letI := S.isClosedImmersion
  letI : Mono S.inclusion.hom.hom := Over.mono_of_mono_left _
  refine ⟨mapPoints (polynomialEvaluate R 0) p, ⟨p, (cancel_mono S.inclusion.hom.hom).mp ?_, rfl⟩, ?_⟩
  · change (_ ≫ p) ≫ S.inclusion.hom.hom = _
    rw [Category.assoc, hp, ← orbitThroughSubgroup]
    exact hf
  · change (_ ≫ p) ≫ S.inclusion.hom.hom = _
    rw [Category.assoc, hp]
    exact hz

/-- The intersection with an ambient limit subgroup is the limit subgroup
inside any closed subgroup containing the cocharacter. -/
private theorem limitIntersection (A : AffineAlgebraicGroup k)
    {P Q I : ClosedSubgroup A.val} (hI : IsSchemeIntersection {P, Q} I)
    (c : Cocharacter Q.group) (E : LimitDecomposition c)
    (D : LimitDecomposition (c ≫ Q.inclusion)) (hP : SameSubgroup P D.parabolic) :
    SameSubgroup I (subgroupOfSubgroup Q E.parabolic) := by
  obtain ⟨i, hi⟩ := (subgroup_of_intersection hI).mp
    (show IsSubgroupOf I I from ⟨𝟙 _, Category.id_comp _⟩) Q (by simp)
  have ha : IsAffine I.group.X.left :=
    (closedSubgroupAlgebraicGroup I).property.1
  have hiP := (subgroup_of_intersection hI).mp
    (show IsSubgroupOf I I from ⟨𝟙 _, Category.id_comp _⟩) P (by simp)
  refine ⟨?_, (subgroup_of_intersection hI).mpr ?_⟩
  · obtain ⟨j, hj⟩ := subgroupInclusionFactors ha E.parabolic i (fun R p ↦ by
      let pQ := pointHom i R p
      have hp : pointHom Q.inclusion R pQ ∈ SubgroupSections D.parabolic _ := by
        apply sections_of_subgroup (subgroupTrans hiP hP.1)
        refine ⟨p, ?_⟩
        change p ≫ I.inclusion.hom.hom = (p ≫ i.hom.hom) ≫ Q.inclusion.hom.hom
        exact (congrArg (fun f : I.group ⟶ A.val ↦ p ≫ f.hom.hom) hi).symm.trans
          (Category.assoc _ _ _).symm
      obtain ⟨z, hz⟩ := (D.parabolic_points R _).mpr hp
      obtain ⟨w, hw, _⟩ := restrictLimit A Q c pQ z hz
      exact (E.parabolic_points R pQ).mp ⟨w, hw⟩)
    exact ⟨j, by change j ≫ (E.parabolic.inclusion ≫ Q.inclusion) = I.inclusion
                 rw [← Category.assoc, hj, hi]⟩
  · rintro J (rfl | rfl)
    · obtain ⟨j, hj⟩ := map_limit_parabolic (closedSubgroupAlgebraicGroup Q).property.1
        Q.inclusion E D
      exact subgroupTrans ⟨j, hj⟩ hP.2
    · exact ⟨E.parabolic.inclusion, rfl⟩

private theorem limitParabolicCast {c d : Cocharacter G} (h : c = d)
    (D : LimitDecomposition d) :
    (show LimitDecomposition c from h.symm ▸ D).parabolic = D.parabolic := by
  subst d
  rfl

private theorem intersectionGeometryOverClosedField [IsAlgClosed k]
    (rational : RationalParabolic.{u}) (throughTorus : RationalParabolicThroughTorus.{u})
    (A : AffineAlgebraicGroup k) (P Q I : ClosedSubgroup A.val)
    (hP : IsParabolic A P) (hQ : IsParabolic A Q)
    (hI : IsSchemeIntersection {P, Q} I)
    (T : ClosedSubgroup A.val) (hT : IsMaximalTorus T)
    (hTP : IsSubgroupOf T P) (hTQ : IsSubgroupOf T Q) :
    Smooth I.group.X.hom ∧ GeometricallyConnected I.group.X.hom := by
  obtain ⟨a, ha⟩ := hTP
  obtain ⟨b, hb⟩ := hTQ
  let S := restrictSubgroup T P a ha
  have hS : IsMaximalTorus S :=
    local_maximal_of_ambient P S ((compose_restrict T P a ha).symm ▸ hT)
  obtain ⟨c, D, hD, _, _⟩ := throughTorus A P hP S hS
  let cQ : Cocharacter Q.group := c ≫ b
  have hc : cQ ≫ Q.inclusion = c ≫ (subgroupOfSubgroup P S).inclusion := by
    change (c ≫ b) ≫ Q.inclusion = c ≫ (a ≫ P.inclusion)
    rw [Category.assoc, ha, hb]
  let AQ := closedSubgroupAlgebraicGroup Q
  letI : Smooth AQ.val.X.hom := hQ.2.1
  letI : ConnectedSpace AQ.val.X.left := parabolicConnected rational A Q hQ
  obtain ⟨E⟩ := existsLimitDecomposition AQ cQ
  let D' : LimitDecomposition (cQ ≫ Q.inclusion) := hc.symm ▸ D
  have hD' : SameSubgroup P D'.parabolic := by
    rw [show D'.parabolic = D.parabolic from limitParabolicCast hc D]
    exact hD
  have hi := limitIntersection A hI cQ E D' hD'
  obtain ⟨e, _⟩ := subgroupOf_mutual_iso hi.1 hi.2
  exact subgroupGeometryOfIso e (limitSubgroupsSmooth AQ cQ E).1
    (geometricallyConnectedLimitSubgroups AQ cQ E).1

private theorem intersectionSmoothConnected
    (rational : RationalParabolic.{u}) (throughTorus : RationalParabolicThroughTorus.{u})
    (A : AffineAlgebraicGroup k) (P Q : ClosedSubgroup A.val)
    (hP : IsParabolic A P) (hQ : IsParabolic A Q) :
    CommonGeometricMaximalTorus P Q ∧ Smooth (intersection P Q).group.X.hom ∧
      GeometricallyConnected (intersection P Q).group.X.hom := by
  let K := AlgebraicClosure k
  have hT := commonGeometricTorus A hP hQ
  refine ⟨hT, ?_⟩
  obtain ⟨_, _, T, hmax, hTP, hTQ⟩ := hT
  obtain ⟨hs, hc⟩ := intersectionGeometryOverClosedField rational throughTorus
    (GeometricGroup A) (extendSubgroup K P) (extendSubgroup K Q)
    (extendSubgroup K (intersection P Q))
    (geometricParabolic A hP) (geometricParabolic A hQ) (baseChangedIntersection K P Q)
    T hmax hTP hTQ
  refine ⟨(smooth_extend_iff K (intersection P Q).group.X).mp hs, ?_⟩
  letI := fieldSpecMap_surjective (k := k) K
  letI : GeometricallyConnected (pullback.snd (intersection P Q).group.X.hom (fieldSpecMap k K)) := hc
  exact geometricallyConnectedOfSurjectiveBaseChange _ (fieldSpecMap k K)


theorem intersectionGeometry_conditional
    (rational : RationalParabolic.{u}) (throughTorus : RationalParabolicThroughTorus.{u}) :
    IntersectionGeometry.{u} := by
  intro k _ A P Q hP hQ
  obtain ⟨hT, hgeom⟩ := intersectionSmoothConnected rational throughTorus A P Q hP hQ
  refine ⟨hT, intersection P Q, pullbackIntersection P Q, hgeom.1, hgeom.2, ?_⟩
  obtain ⟨_, _, T, hmax, hTP, hTQ⟩ := hT
  let K := AlgebraicClosure k
  refine ⟨(extendSubgroup K (intersection P Q)).isClosedImmersion, T, hmax,
    (subgroup_of_intersection (baseChangedIntersection K P Q)).mpr ?_⟩
  intro W hW
  have hcases : W = extendSubgroup K P ∨ W = extendSubgroup K Q := by simpa using hW
  rcases hcases with rfl | rfl
  · exact hTP
  · exact hTQ

/-- The inverse image as a closed subgroup, with its projection to the given
subgroup. -/
private def preimageSubgroup {L : GroupScheme k} (f : G ⟶ L)
    (I : ClosedSubgroup L) : ClosedSubgroup G := by
  let a := pullback.fst f I.inclusion
  have square := ((Grp.forget (SchemeOver k) ⋙ Over.forget _)).map_isPullback
    (IsPullback.of_hasPullback f I.inclusion)
  exact ⟨_, a, MorphismProperty.of_isPullback square.flip I.isClosedImmersion⟩

private theorem preimageSquare {L : GroupScheme k} (f : G ⟶ L) (I : ClosedSubgroup L) :
    IsPullback (preimageSubgroup f I).inclusion.hom.hom
      (pullback.snd f I.inclusion).hom.hom f.hom.hom I.inclusion.hom.hom :=
  (Grp.forget (SchemeOver k)).map_isPullback (IsPullback.of_hasPullback f I.inclusion)

/-- Multiplication by a lift followed by a kernel element exhibits the
product map as the base change of the map onto the image. -/
private theorem productPullback {H L : GroupScheme k} (a : H ⟶ G) {f : G ⟶ L}
    {I : ClosedSubgroup L} {p : H ⟶ I.group} (hp : p ≫ I.inclusion = a ≫ f)
    {J : ClosedSubgroup G} {q : J.group ⟶ I.group}
    (hJ : IsPullback J.inclusion.hom.hom q.hom.hom f.hom.hom I.inclusion.hom.hom)
    {U : ClosedSubgroup G} (hU : IsSchemeKernel f U) :
    ∃ m : H.X ⊗ U.group.X ⟶ J.group.X,
      m ≫ J.inclusion.hom.hom = multiplyFactors a U.inclusion ∧
        IsPullback m (fst H.X U.group.X) q.hom.hom p.hom.hom := by
  let x := multiplyFactors a U.inclusion
  let y := fst H.X U.group.X ≫ p.hom.hom
  have ha : a.hom.hom ≫ f.hom.hom = p.hom.hom ≫ I.inclusion.hom.hom :=
    congrArg (fun g : H ⟶ L ↦ g.hom.hom) hp.symm
  have hx : x ≫ f.hom.hom = y ≫ I.inclusion.hom.hom := by
    have hu : (snd H.X U.group.X ≫ U.inclusion.hom.hom) ≫ f.hom.hom = 1 :=
      (schemeKernel_sections hU _).mp ⟨snd H.X U.group.X, rfl⟩
    simp only [x, multiplyFactors, y, MonObj.mul_comp, hu, mul_one, Category.assoc, ha]
  let m := hJ.lift x y hx
  have hm : m ≫ J.inclusion.hom.hom = x := hJ.lift_fst x y hx
  have hm' : m ≫ q.hom.hom = y := hJ.lift_snd x y hx
  refine ⟨m, hm, IsPullback.mk' hm' ?_ ?_⟩
  · intro X v w h₁ h₂
    apply CartesianMonoidalCategory.hom_ext v w h₂
    let := U.isClosedImmersion
    let : Mono U.inclusion.hom.hom := Over.mono_of_mono_left _
    apply (cancel_mono U.inclusion.hom.hom).mp
    have he : v ≫ x = w ≫ x := by
      simpa only [Category.assoc, hm] using congrArg (· ≫ J.inclusion.hom.hom) h₁
    simp only [x, multiplyFactors, MonObj.comp_mul, ← Category.assoc, h₂] at he
    exact mul_left_cancel he
  · intro X j h he
    let d := (h ≫ a.hom.hom)⁻¹ * (j ≫ J.inclusion.hom.hom)
    have hd : (j ≫ J.inclusion.hom.hom) ≫ f.hom.hom = (h ≫ a.hom.hom) ≫ f.hom.hom := by
      rw [Category.assoc, hJ.w, ← Category.assoc j, he]
      simp only [Category.assoc, ha]
    have hd' : d ≫ f.hom.hom = 1 := by
      simp only [d, MonObj.mul_comp, GrpObj.inv_comp, hd, inv_mul_cancel]
    obtain ⟨u, hu⟩ := (schemeKernel_sections hU d).mpr hd'
    change u ≫ U.inclusion.hom.hom = d at hu
    refine ⟨lift h u, ?_, lift_fst _ _⟩
    apply hJ.hom_ext
    · rw [Category.assoc, hm]
      simp only [x, multiplyFactors, MonObj.comp_mul, ← Category.assoc, lift_fst, lift_snd, hu]
      exact mul_inv_cancel_left _ _
    · rw [Category.assoc, hm']
      change lift h u ≫ fst H.X U.group.X ≫ p.hom.hom = _
      rw [← Category.assoc, lift_fst, he]

private theorem productFppf {H L : GroupScheme k} (a : H ⟶ G) {f : G ⟶ L}
    {I : ClosedSubgroup L} {p : H ⟶ I.group} (hp : IsImageFactorization (a ≫ f) p I.inclusion)
    {J : ClosedSubgroup G} {q : J.group ⟶ I.group}
    (hJ : IsPullback J.inclusion.hom.hom q.hom.hom f.hom.hom I.inclusion.hom.hom)
    {U : ClosedSubgroup G} (hU : IsSchemeKernel f U) :
    ∃ m : H.X ⊗ U.group.X ⟶ J.group.X,
      m ≫ J.inclusion.hom.hom = multiplyFactors a U.inclusion ∧
        Flat m.left ∧ Surjective m.left ∧ LocallyOfFinitePresentation m.left ∧ IsAffineHom m.left := by
  obtain ⟨m, hm, hSquare⟩ := productPullback a hp.1 hJ hU
  have hBase := (Over.forget _).map_isPullback hSquare.flip
  exact ⟨m, hm, MorphismProperty.of_isPullback hBase hp.2.1,
    MorphismProperty.of_isPullback hBase hp.2.2.1,
    MorphismProperty.of_isPullback hBase hp.2.2.2.1,
    MorphismProperty.of_isPullback hBase hp.2.2.2.2.1⟩

private theorem limitSmooth {c : Cocharacter G} (D : LimitDecomposition c)
    (hs : Smooth D.contracting.group.X.hom) : Smooth D.limit.hom.hom.left := by
  let m := multiplyFactors D.sectionMap D.contractingToParabolic
  letI : IsIso m := D.product_iso
  letI : IsIso m.left := (Over.forget _).map_isIso m
  have hsection : D.sectionMap.hom.hom ≫ D.limit.hom.hom = 𝟙 D.centralizer.group.X :=
    congrArg (fun f : D.centralizer.group ⟶ D.centralizer.group ↦ f.hom.hom) D.section_limit
  have hkernel : D.contractingToParabolic.hom.hom ≫ D.limit.hom.hom = 1 := D.isKernel.w
  have he : m ≫ D.limit.hom.hom = fst D.centralizer.group.X D.contracting.group.X := by
    simp only [m, multiplyFactors, MonObj.mul_comp, Category.assoc]
    rw [hsection, hkernel, Category.comp_id, MonObj.comp_one, mul_one]
  have hfst : Smooth (fst D.centralizer.group.X D.contracting.group.X).left := by
    letI := hs
    change Smooth (pullback.fst D.centralizer.group.X.hom D.contracting.group.X.hom)
    infer_instance
  apply (MorphismProperty.cancel_left_of_respectsIso @Smooth m.left _).mp
  have heLeft : m.left ≫ D.limit.hom.hom.left =
      (fst D.centralizer.group.X D.contracting.group.X).left :=
    congrArg (fun f : (D.centralizer.group.X ⊗ D.contracting.group.X) ⟶
      D.centralizer.group.X ↦ f.left) he
  exact heLeft.symm ▸ hfst

/-- A faithfully flat image of a smooth group is geometrically reduced, hence
smooth. Check reducedness after passing to the algebraic closure. -/
private theorem smoothImage (A L : AffineAlgebraicGroup k) (p : A.val ⟶ L.val)
    (hflat : Flat p.hom.hom.left) (hsurj : Surjective p.hom.hom.left)
    (hA : Smooth A.val.X.hom) : Smooth L.val.X.hom := by
  let K := AlgebraicClosure k
  let pK := (groupBaseChange k K).map p
  let AK := GeometricGroup A
  let LK := GeometricGroup L
  have hpb := (baseChangeMapPullback (K := K) p.hom.hom).flip
  have hflatK : Flat pK.hom.hom.left := MorphismProperty.of_isPullback hpb hflat
  have hsurjK : Surjective pK.hom.hom.left := MorphismProperty.of_isPullback hpb hsurj
  letI : Smooth AK.val.X.hom := (smooth_extend_iff K A.val.X).mpr hA
  letI : IsReduced AK.val.X.left := isReduced_of_smooth_over_field AK.val.X.hom
  have hred : IsReduced LK.val.X.left :=
    reduced_of_flat_local_cover (X := AK.val.X.left) fun z ↦ by
      obtain ⟨x, hx⟩ := hsurjK.1 z
      exact ⟨pK.hom.hom.left, hflatK, x, hx⟩
  letI := LK.property.2.1
  exact (smooth_extend_iff K L.val.X).mp (smoothOfReducedOverPerfectField K LK.val hred)

private theorem smoothPreimage {L : GroupScheme k} {f : G ⟶ L} {I : ClosedSubgroup L}
    {J : ClosedSubgroup G} {q : J.group ⟶ I.group}
    (h : IsPullback J.inclusion.hom.hom q.hom.hom f.hom.hom I.inclusion.hom.hom)
    (hf : Smooth f.hom.hom.left) (hI : Smooth I.group.X.hom) : Smooth J.group.X.hom := by
  letI : Smooth q.hom.hom.left :=
    MorphismProperty.of_isPullback ((Over.forget _).map_isPullback h) hf
  letI := hI
  rw [← Over.w q.hom.hom]
  infer_instance

/-- For a split quotient, the difference between a section and the lift of its
image factors through the scheme kernel. -/
private theorem differenceInKernel {L : GroupScheme k} {p : G ⟶ L} {s : L ⟶ G}
    (hs : s ≫ p = 𝟙 L) {U : ClosedSubgroup G} (hU : IsSchemeKernel p U)
    {X : SchemeOver k} (x : X ⟶ G.X) :
    x * (x ≫ p.hom.hom ≫ s.hom.hom)⁻¹ ∈ SubgroupSections U X := by
  apply (schemeKernel_sections hU _).mpr
  have hs' : s.hom.hom ≫ p.hom.hom = 𝟙 L.X :=
    congrArg (fun f : L ⟶ L ↦ f.hom.hom) hs
  simp only [MonObj.mul_comp, GrpObj.inv_comp, Category.assoc, hs',
    Category.comp_id, mul_inv_cancel]

private theorem factorThroughSplitQuotient {L M : GroupScheme k}
    {p : G ⟶ L} {s : L ⟶ G} (hs : s ≫ p = 𝟙 L)
    {U : ClosedSubgroup G} (hU : IsSchemeKernel p U)
    {q : G ⟶ M} {V : ClosedSubgroup G} (hV : IsSchemeKernel q V)
    (hUV : IsSubgroupOf U V) : p ≫ s ≫ q = q := by
  apply Grp.hom_ext
  have h := (schemeKernel_sections hV _).mp
    (sections_of_subgroup hUV (differenceInKernel hs hU (𝟙 G.X)))
  simp only [Category.id_comp, MonObj.mul_comp, GrpObj.inv_comp, Category.assoc] at h
  exact (mul_inv_eq_one.mp h).symm

private theorem splitQuotientIso {L M : GroupScheme k}
    {p : G ⟶ L} {s : L ⟶ G} (hs : s ≫ p = 𝟙 L)
    {q : G ⟶ M} {t : M ⟶ G} (ht : t ≫ q = 𝟙 M)
    {U V : ClosedSubgroup G} (hU : IsSchemeKernel p U) (hV : IsSchemeKernel q V)
    (hUV : SameSubgroup U V) : ∃ e : L ≅ M, p ≫ e.hom = q := by
  have hp := factorThroughSplitQuotient hs hU hV hUV.1
  have hq := factorThroughSplitQuotient ht hV hU hUV.2
  refine ⟨⟨s ≫ q, t ≫ p, ?_, ?_⟩, hp⟩
  · rw [Category.assoc, hq, hs]
  · rw [Category.assoc, hp, ht]

private theorem limitKernelUnderIso {c : Cocharacter G} (D : LimitDecomposition c)
    {P : GroupScheme k} (e : P ≅ D.parabolic.group) :
    IsSchemeKernel (e.hom ≫ D.limit) (pushSubgroup e.symm (contractingSubgroup D)) := by
  change IsPullback (D.contractingToParabolic ≫ e.inv).hom.hom
    (toUnit D.contracting.group.X) (e.hom ≫ D.limit).hom.hom η[D.centralizer.group.X]
  simpa only [Iso.symm_hom, Iso.symm_inv, Iso.refl_inv, Category.comp_id] using
    transportedLimitKernel D (Iso.refl D.centralizer.group) e.symm

private theorem borelUnderIso {L : GroupScheme k} (e : G ≅ L) {B : ClosedSubgroup G}
    (hB : IsBorel B) : IsBorel (transportSubgroup e B) := by
  refine ⟨hB.1, ?_⟩
  intro J hJ h
  obtain ⟨i, hi⟩ := h
  change i ≫ J.inclusion = B.inclusion ≫ e.hom at hi
  have hj : IsSubgroupOf B (transportSubgroup e.symm J) := ⟨i, by
    change i ≫ J.inclusion ≫ e.inv = B.inclusion
    rw [← Category.assoc, hi, Category.assoc, e.hom_inv_id, Category.comp_id]⟩
  obtain ⟨j, hj'⟩ := hB.2 (transportSubgroup e.symm J) hJ hj
  refine ⟨j, ?_⟩
  change j ≫ B.inclusion = J.inclusion ≫ e.inv at hj'
  change j ≫ B.inclusion ≫ e.hom = J.inclusion
  rw [← Category.assoc, hj', Category.assoc, e.inv_hom_id, Category.comp_id]

private theorem conjugationNaturality {L : GroupScheme k} (f : G ⟶ L)
    (g : 𝟙_ (SchemeOver k) ⟶ G.X) :
    (conjugationIso g).hom ≫ f = f ≫ (conjugationIso (g ≫ f.hom.hom)).hom := by
  apply Grp.hom_ext
  change conjugate g (𝟙 G.X) ≫ f.hom.hom =
    f.hom.hom ≫ conjugate (g ≫ f.hom.hom) (𝟙 L.X)
  rw [conjugate_comp, comp_conjugate, Category.id_comp, Category.comp_id]

/-- The standard presentation supplies a subtorus centralizer for the Levi
and places its contracting group inside the chosen Borel. -/
private theorem standardLevi [IsAlgClosed k] (A : AffineAlgebraicGroup k)
    {P B T : ClosedSubgroup A.val} (hP : IsParabolic A P) (hB : IsBorel B)
    (hBP : IsSubgroupOf B P) (hT : IsMaximalTorus T) (hTB : IsSubgroupOf T B) :
    ∃ (S : ClosedSubgroup A.val) (c : Cocharacter A.val) (D : LimitDecomposition c),
      IsTorus S.group ∧ IsSubgroupOf S T ∧ IsCentralizer S D.centralizer ∧
      SameSubgroup P D.parabolic ∧ IsReductive (closedSubgroupAlgebraicGroup D.centralizer) ∧
      IsContractingRadical D ∧ IsSubgroupOf D.contracting B := by
  obtain ⟨hcomm, D, W, U, c, b, hreg, hroots, hbase, hn, Ps, hindices, hclassify⟩ :=
    LinearAlgebraicGroups.Flag.StandardParabolics.standardParabolicClassification A hP.1 T B
      (split_of_maximal hT) (geometricMaximal_of_maximal A T hT)
      ((isKBorel_iff_of_isAlgClosed A B).mpr hB) hTB
  letI := hcomm
  obtain ⟨⟨i, hi, _⟩, he⟩ := hclassify P hP hBP
  let E := Ps i
  refine ⟨subgroupOfSubgroup T E.kernelTorus, _, E.limitGroups,
    lattice_torus_of_split E.isKernelTorus.1, ⟨E.kernelTorus.inclusion, rfl⟩,
    E.centralizer, (he i).mp hi, E.leviSplit.1, E.radical, E.radicalInBorel⟩

/-- Projection to the standard Levi sends the chosen Borel into its
intersection with the Levi. -/
private theorem limitOfBorel {c : Cocharacter G} (D : LimitDecomposition c)
    {B : ClosedSubgroup G} {b : B.group ⟶ D.parabolic.group}
    (hb : b ≫ D.parabolic.inclusion = B.inclusion)
    (hu : IsSubgroupOf D.contracting B)
    {F : ClosedSubgroup D.centralizer.group}
    (hF : IsSchemeIntersection {D.centralizer, B} (subgroupOfSubgroup D.centralizer F)) :
    ∃ f : B.group ⟶ F.group, f ≫ F.inclusion = b ≫ D.limit := by
  let x := b.hom.hom
  let y := x ≫ D.limit.hom.hom ≫ D.sectionMap.hom.hom
  let i := D.parabolic.inclusion.hom.hom
  have hx : x ≫ i = B.inclusion.hom.hom :=
    congrArg (fun f : B.group ⟶ G ↦ f.hom.hom) hb
  have huv : IsSubgroupOf (subgroupOfSubgroup D.parabolic (contractingSubgroup D)) B := by
    obtain ⟨j, hj⟩ := hu
    exact ⟨j, hj.trans D.contracting_in_G.symm⟩
  obtain ⟨v, hv⟩ := differenceInKernel D.section_limit
    (show IsSchemeKernel D.limit (contractingSubgroup D) from D.isKernel) x
  have hv' : (x * y⁻¹) ≫ i ∈ SubgroupSections B B.group.X := by
    apply sections_of_subgroup huv
    exact ⟨v, by
      change v ≫ D.contractingToParabolic.hom.hom ≫ i = _
      rw [← Category.assoc]
      exact congrArg (· ≫ i) hv⟩
  have hy : y ≫ i ∈ SubgroupSections B B.group.X := by
    have hx' : x ≫ i ∈ SubgroupSections B B.group.X := ⟨𝟙 _, (Category.id_comp _).trans hx.symm⟩
    convert (SubgroupSections B B.group.X).mul_mem
      ((SubgroupSections B B.group.X).inv_mem hv') hx' using 1
    rw [← GrpObj.inv_comp, ← MonObj.mul_comp]
    congr 1
    group
  have he : y ≫ i = (b ≫ D.limit).hom.hom ≫ D.centralizer.inclusion.hom.hom := by
    have h := congrArg (fun f : D.centralizer.group ⟶ G ↦ f.hom.hom) D.section_in_G
    change D.sectionMap.hom.hom ≫ i = _ at h
    change (x ≫ D.limit.hom.hom ≫ D.sectionMap.hom.hom) ≫ i =
      (x ≫ D.limit.hom.hom) ≫ D.centralizer.inclusion.hom.hom
    simpa only [Category.assoc, h]
  obtain ⟨z, hz⟩ := (hF _ (y ≫ i)).mpr (by
    rintro C (rfl | rfl)
    · exact ⟨(b ≫ D.limit).hom.hom, he.symm⟩
    · exact hy)
  apply factor_group_through_subgroup F (b ≫ D.limit) z
  letI := D.centralizer.isClosedImmersion
  letI : Mono D.centralizer.inclusion.hom.hom := Over.mono_of_mono_left _
  apply (cancel_mono D.centralizer.inclusion.hom.hom).mp
  change (z ≫ F.inclusion.hom.hom) ≫ D.centralizer.inclusion.hom.hom = _
  rw [Category.assoc]
  exact hz.trans he

/-- A split projection with the radical as kernel has the same quotient as the
standard geometric Levi. A Borel from each of the two parabolics gives a
Borel in the projected intersection and a lift of one to its inverse image. -/
private theorem projectionBorels [IsAlgClosed k] (A : AffineAlgebraicGroup k)
    {P Q H B C : ClosedSubgroup A.val}
    (hP : IsParabolic A P) (hB : IsBorel B) (hC : IsBorel C)
    (hBP : IsSubgroupOf B P) (hCQ : IsSubgroupOf C Q)
    (hH : IsSchemeIntersection {P, Q} H) {a : H.group ⟶ P.group}
    (ha : a ≫ P.inclusion = H.inclusion)
    {L : GroupScheme k} {p : P.group ⟶ L} {s : L ⟶ P.group} (hs : s ≫ p = 𝟙 L)
    {U : ClosedSubgroup P.group} (hU : IsSchemeKernel p U)
    (hRu : IsUnipotentRadical (closedSubgroupAlgebraicGroup P) U)
    {I : ClosedSubgroup L} {pH : H.group ⟶ I.group} (hpH : pH ≫ I.inclusion = a ≫ p)
    {J : ClosedSubgroup P.group} {q : J.group ⟶ I.group}
    (hJ : IsPullback J.inclusion.hom.hom q.hom.hom p.hom.hom I.inclusion.hom.hom) :
    (∃ F : ClosedSubgroup L, IsBorel F ∧ IsSubgroupOf F I) ∧
      ∃ E : ClosedSubgroup A.val, IsBorel E ∧ IsSubgroupOf E (subgroupOfSubgroup P J) := by
  obtain ⟨T, hT, hTB, hTC⟩ := commonTorusInBorels A hP.1 hB hC
  obtain ⟨S, c, D, hS, hST, hZ, hSame, hL, hR, hRB⟩ := standardLevi A hP hB hBP hT hTB
  obtain ⟨e, he⟩ := subgroupOf_mutual_iso hSame.1 hSame.2
  let f := e.hom ≫ D.limit
  let t := D.sectionMap ≫ e.inv
  have htf : t ≫ f = 𝟙 _ := by
    simp only [t, f, Category.assoc, e.inv_hom_id_assoc, D.section_limit]
  let V := pushSubgroup e.symm (contractingSubgroup D)
  have hV : IsSchemeKernel f V := limitKernelUnderIso D e
  have hRv : IsUnipotentRadical (closedSubgroupAlgebraicGroup P) V :=
    radical_transport (A := closedSubgroupAlgebraicGroup D.parabolic)
      (B := closedSubgroupAlgebraicGroup P) e.symm (contractingSubgroup D) hR.1
  have hVU : SameSubgroup V U :=
    ⟨hRu.2.2 V hRv.1 hRv.2.1, hRv.2.2 U hRu.1 hRu.2.1⟩
  obtain ⟨φ, hφ⟩ := splitQuotientIso htf hs hV hU hVU
  have hcentralizerBorel := LinearAlgebraicGroups.Reductive.SubtorusCentralizer.centralizerBorel
    A hP.1.1 (connected_of_reductive A hP.1) T S hT hS hST D.centralizer hZ
  obtain ⟨B₁, hB₁, hBor₁⟩ := hcentralizerBorel B hB hTB
  obtain ⟨B₂, hB₂, hBor₂⟩ := hcentralizerBorel C hC hTC
  have htP : t ≫ P.inclusion = D.centralizer.inclusion := by
    change (D.sectionMap ≫ e.inv) ≫ P.inclusion = _
    rw [← he, Category.assoc, e.inv_hom_id_assoc, D.section_in_G]
  obtain ⟨d, hd⟩ := (subgroup_of_intersection (H := subgroupOfSubgroup D.centralizer B₂) hH).mpr (by
      intro E hE
      have h : E = P ∨ E = Q := by simpa using hE
      rcases h with h | h
      · rw [h]
        exact ⟨B₂.inclusion ≫ t, by rw [Category.assoc, htP]; rfl⟩
      · rw [h]
        exact subgroupTrans ((subgroup_of_intersection hB₂).mp
          ⟨𝟙 _, Category.id_comp _⟩ C (by simp)) hCQ)
  letI := inclusion_mono P
  have hda : d ≫ a = B₂.inclusion ≫ t := by
    apply (cancel_mono P.inclusion).mp
    rw [Category.assoc, ha, hd, Category.assoc, htP]
    rfl
  have hdI : (d ≫ pH) ≫ I.inclusion = B₂.inclusion ≫ φ.hom := by
    rw [Category.assoc, hpH, ← Category.assoc d, hda]
    rw [Category.assoc, ← hφ, ← Category.assoc t, htf, Category.id_comp]
  refine ⟨⟨transportSubgroup φ B₂, borelUnderIso φ hBor₂, ⟨d ≫ pH, hdI⟩⟩, ?_⟩
  obtain ⟨g, eB, hconj⟩ := LinearAlgebraicGroups.GeometricBorelConjugacy.borelsConjugate
    (closedSubgroupAlgebraicGroup D.centralizer) hL.1 (connected_of_reductive _ hL)
    B₁ B₂ hBor₁ hBor₂
  change (𝟙_ (SchemeOver k) ⟶ D.centralizer.group.X) at g
  have heB : eB.hom ≫ B₂.inclusion = B₁.inclusion ≫ (conjugationIso g).hom := by
    apply Grp.hom_ext
    change (eB.hom ≫ B₂.inclusion).hom.hom =
      B₁.inclusion.hom.hom ≫ conjugate g (𝟙 D.centralizer.group.X)
    rw [comp_conjugate, Category.comp_id]
    exact hconj
  obtain ⟨b, hb⟩ := hBP
  obtain ⟨b₁, hb₁⟩ := limitOfBorel D (b := b ≫ e.hom)
    (by rw [Category.assoc, he, hb]) hRB hB₁
  have hb₁' : b₁ ≫ B₁.inclusion = b ≫ f := by
    simpa only [f, Category.assoc] using hb₁
  let gP := g ≫ t.hom.hom
  let b' := b ≫ (conjugationIso gP).hom
  let E := transportSubgroup (conjugationIso (gP ≫ P.inclusion.hom.hom)) B
  have hb' : b' ≫ P.inclusion = E.inclusion := by
    change (b ≫ (conjugationIso gP).hom) ≫ P.inclusion =
      B.inclusion ≫ (conjugationIso (gP ≫ P.inclusion.hom.hom)).hom
    rw [Category.assoc, conjugationNaturality, ← Category.assoc, hb]
  have hg : gP ≫ f.hom.hom = g := by
    change (g ≫ t.hom.hom) ≫ f.hom.hom = g
    rw [Category.assoc, show t.hom.hom ≫ f.hom.hom = 𝟙 D.centralizer.group.X from
      congrArg (fun m : D.centralizer.group ⟶ D.centralizer.group ↦ m.hom.hom) htf,
      Category.comp_id]
  have hb'f : b' ≫ f = b₁ ≫ eB.hom ≫ B₂.inclusion := by
    change (b ≫ (conjugationIso gP).hom) ≫ f = _
    calc
      _ = b ≫ ((conjugationIso gP).hom ≫ f) := Category.assoc _ _ _
      _ = b ≫ (f ≫ (conjugationIso g).hom) := by rw [conjugationNaturality f gP, hg]
      _ = (b ≫ f) ≫ (conjugationIso g).hom := (Category.assoc _ _ _).symm
      _ = _ := by rw [← hb₁', Category.assoc, ← heB]
  let v := b₁ ≫ eB.hom ≫ d ≫ pH
  have h : b' ≫ p = v ≫ I.inclusion := by
    calc
      b' ≫ p = b' ≫ (f ≫ φ.hom) := congrArg (b' ≫ ·) hφ.symm
      _ = (b' ≫ f) ≫ φ.hom := (Category.assoc _ _ _).symm
      _ = b₁ ≫ eB.hom ≫ B₂.inclusion ≫ φ.hom := by
        rw [hb'f]
        simp only [Category.assoc]
      _ = v ≫ I.inclusion := by
        rw [hdI.symm.trans (Category.assoc _ _ _)]
        simp only [v, Category.assoc]
  have h' : b'.hom.hom ≫ p.hom.hom = v.hom.hom ≫ I.inclusion.hom.hom :=
    congrArg (fun m : B.group ⟶ L ↦ m.hom.hom) h
  obtain ⟨j, hj⟩ := factor_group_through_subgroup J b'
    (hJ.lift b'.hom.hom v.hom.hom h') (hJ.lift_fst _ _ _)
  exact ⟨E, borelUnderIso _ hB, ⟨j, by
    change j ≫ J.inclusion ≫ P.inclusion = E.inclusion
    rw [← Category.assoc, hj, hb']⟩⟩

theorem intersectionProjection_conditional
    (rational : RationalParabolic.{u}) (throughTorus : RationalParabolicThroughTorus.{u}) :
    IntersectionProjection.{u} := by
  intro k _ A P Q hP hQ
  let H := intersection P Q
  let a := pullback.fst P.inclusion Q.inclusion
  have ha : a ≫ P.inclusion = H.inclusion := rfl
  obtain ⟨_, hHs, _⟩ := intersectionSmoothConnected rational throughTorus A P Q hP hQ
  obtain ⟨c, D, hSame, hL, hR⟩ := rational A P hP
  obtain ⟨e, he⟩ := subgroupOf_mutual_iso hSame.1 hSame.2
  let f := e.hom ≫ D.limit
  let s := D.sectionMap ≫ e.inv
  have hs : s ≫ f = 𝟙 _ := by
    simp only [s, f, Category.assoc, e.inv_hom_id_assoc, D.section_limit]
  let L := closedSubgroupAlgebraicGroup D.centralizer
  obtain ⟨M, p, i, hp, hp', _⟩ := schemeImageFactorization (closedSubgroupAlgebraicGroup H) L (a ≫ f)
  let I : ClosedSubgroup L.val := ⟨M.val, i, hp.2.2.2.2.2⟩
  let J := preimageSubgroup f I
  let q := pullback.snd f I.inclusion
  have hJ : IsPullback J.inclusion.hom.hom q.hom.hom f.hom.hom I.inclusion.hom.hom :=
    preimageSquare f I
  have hIs : Smooth I.group.X.hom :=
    smoothImage (closedSubgroupAlgebraicGroup H) M p hp.2.1 hp.2.2.1 hHs
  have hf : Smooth f.hom.hom.left := by
    letI : IsIso e.hom.hom.hom.left := (Grp.forget (SchemeOver k) ⋙ Over.forget _).map_isIso e.hom
    letI := limitSmooth D hR.1.1.1
    change Smooth (e.hom.hom.hom.left ≫ D.limit.hom.hom.left)
    infer_instance
  have hJs : Smooth J.group.X.hom := smoothPreimage hJ hf hIs

  let K := AlgebraicClosure k
  let F := groupBaseChange k K
  let Pbar := extendSubgroup K P
  let Qbar := extendSubgroup K Q
  let Hbar := extendSubgroup K H
  let Ibar := extendSubgroup K I
  let Jbar := extendSubgroup K J
  let U := pushSubgroup e.symm (contractingSubgroup D)
  have hU : IsSchemeKernel f U := limitKernelUnderIso D e
  obtain ⟨hRclosed, hRbar⟩ := hR.2
  obtain ⟨_, hRU⟩ := baseChanged_radical_transport
    (A := closedSubgroupAlgebraicGroup D.parabolic) (B := closedSubgroupAlgebraicGroup P)
    e.symm (contractingSubgroup D) hRclosed hRbar
  have hUbar : IsSchemeKernel (F.map f) (extendSubgroup K U) :=
    baseChangeKernelSquare (K := K) f U.inclusion hU
  have hsbar : F.map s ≫ F.map f = 𝟙 _ := by rw [← F.map_comp, hs, F.map_id]
  have hpbar : F.map p ≫ Ibar.inclusion = F.map a ≫ F.map f := by
    change F.map p ≫ F.map i = _
    rw [← F.map_comp, ← F.map_comp, hp.1]
  have hJbar : IsPullback Jbar.inclusion.hom.hom (F.map q).hom.hom
      (F.map f).hom.hom Ibar.inclusion.hom.hom :=
    (baseChange k K).map_isPullback hJ
  obtain ⟨_, B, hB, hBP⟩ := hP.2.2
  obtain ⟨_, C, hC, hCQ⟩ := hQ.2.2
  obtain ⟨⟨BI, hBI, hBII⟩, BJ, hBJ, hBJJ⟩ :=
    projectionBorels (GeometricGroup A) (P := Pbar) (Q := Qbar) (H := Hbar)
      (geometricParabolic A hP) hB hC hBP hCQ
      (baseChangedIntersection K P Q) (a := F.map a)
      ((F.map_comp a P.inclusion).symm.trans (congrArg F.map ha))
      hsbar hUbar hRU hpbar hJbar
  have hBJ' : IsSubgroupOf BJ (extendSubgroup K (subgroupOfSubgroup P J)) := by
    obtain ⟨j, hj⟩ := hBJJ
    refine ⟨j, ?_⟩
    change j ≫ F.map (J.inclusion ≫ P.inclusion) = BJ.inclusion
    rw [F.map_comp]
    exact hj
  obtain ⟨m, hm⟩ := productFppf a hp hJ hU
  exact ⟨H, a, c, D, e, pullbackIntersection P Q, ha, he, hR, I, p, J, q,
    ⟨hL, hIs, Ibar.isClosedImmersion, BI, hBI, hBII⟩, hp, hp', hJ,
    ⟨hP.1, hJs, (extendSubgroup K (subgroupOfSubgroup P J)).isClosedImmersion, BJ, hBJ, hBJ'⟩,
    U, m, hU, hm⟩

/-- Two parabolics have a smooth, geometrically connected scheme intersection
containing a maximal torus after extension to the algebraic closure. -/
theorem intersectionGeometry : IntersectionGeometry.{u} :=
  intersectionGeometry_conditional rationalParabolic rationalParabolicThroughTorus

/-- The image of the intersection in the reductive quotient of the first
parabolic, and its inverse image, are parabolic. -/
theorem intersectionProjection : IntersectionProjection.{u} :=
  intersectionProjection_conditional rationalParabolic rationalParabolicThroughTorus

end

end LinearAlgebraicGroups.Relative.ParabolicIntersection
