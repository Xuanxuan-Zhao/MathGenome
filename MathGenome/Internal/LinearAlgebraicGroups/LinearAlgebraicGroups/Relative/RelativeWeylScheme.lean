import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Relative.RelativeWeylScheme
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Reductive.NormalizerLatticeAction
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Relative.ParabolicIntersection
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Reductive.MaximalToriExist
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Relative.MaximalSplitTori
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Flag.StandardParabolics
import Batteries.Tactic.OpenPrivate

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

universe u

namespace LinearAlgebraicGroups.Relative.RelativeWeylScheme

open _root_.LinearAlgebraicGroups.Specs
open Specs.Relative.RelativeWeylScheme
open Specs.Relative.MaximalSplitTori
open Specs.GeometricBorelConjugacy (ConjugatesSubgroups subgroupOfSubgroup)
open Specs.GeometricRadicals (GeometricGroup IsReductive IsSplitTorus IsTorus IsMaximalTorus)
open Specs.BorelProper (IsParabolic)
open Specs.Unipotent (closedSubgroupAlgebraicGroup)
open Specs.BorelsAndChambers (contractingSubgroup)
open LinearAlgebraicGroups.CocharacterDynamics
open Specs.CharacterDescent (Cocharacter)
open Specs.NormalizerLatticeAction (ConstantGroup)
open LinearAlgebraicGroups.Relative.MaximalSplitTori
open LinearAlgebraicGroups (normalizerSchemeBaseChange)
open Specs.RankOneFlag (SameSubgroup)
open Specs.SchemeDerivedGroup (FactorsThrough IsSubgroupOf)
open Specs.UnipotentRadicalIntersection (IsSchemeIntersection)

open private restrictSubgroup compose_restrict subgroupOfSubgroup_le
  conjugates_trans conjugates_in_ambient conjugates_preserves_borel conjugates_maximal
  conjugationIso conjugate comp_conjugate transportSubgroup conjugates_transport
  normalizes_of_conjugates_self
  local_maximal_of_ambient definingIdeal_prime_of_torus
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Reductive.MaximalToriConjugate
open private subgroupTrans transportSubgroup_le
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Relative.ParabolicIntersection
open private isTorus_of_split from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Descent.FiniteFieldFlags
open private connected_of_reductive normalizes_iff_sections conjugates_transport_ambient
  conjugates_same_target conjugates_of_same conjugates_of_normalizes conjugates_extend
  conjugates_inverse extendSubgroup subgroup_extend subgroup_descend
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.RootData.BorelNormalizer
open private sections_of_subgroup subgroup_of_intersection
  torus_in_limit_parabolic
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Reductive.UnipotentRadicalIntersection
open private subgroupOf_mutual_iso factor_group_through_subgroup
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Reductive.GeometricBorelConjugacy
open private centralizes_iff mono_over from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Affine.Stabilizers
open private extensionAdj adjoint_family conjugation_baseChange whisker_conjugation
  prodComparison_inv_fst conjugation adjoint_factorization from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Affine.Stabilizers
open private definingIdeal definingIdeal_le factor_iso_of_definingIdeal_eq
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Reductive.GeometricRadicals
open private torus_commutative from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Reductive.TorusFreeUnipotent
open private radical_transport pushSubgroup from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.RootData.OrderedRootProducts
open private maximalSplitOfConjugate limitIsParabolic minimalParabolicTransport
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Relative.MaximalSplitTori
open private geometricFibres_of_fppf from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Reductive.NormalizerLatticeAction
open private gm_baseChange from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Reductive.CocharacterLimitSubgroups
open private pushLimitParabolic limitParabolic_transport from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Relative.RationalCocharacter
open private limits_subgroups_extend from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.RootData.RankOneFlag
open private schemeKernel_sections from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Affine.SchemeImageQuotient

open private comp_conjugateFamily from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Affine.Stabilizers
open private scalarExtendedPoint_natural scalarExtended_point_injective
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.RootData.RankOneFlag
open private subgroup_normalizes from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.RootData.BorelNormalizer
open private connected_of_geometricallyConnected from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.RootData.BorelsAndChambers
open private torus_after_algClosed_extension from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Reductive.MaximalToriExist
open private leviCentralizesSplitTorus splitTorusImage from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Relative.MaximalSplitTori
open private multiplicative_group_iso from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Relative.LeviConjugacy

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
set_option linter.style.haveILetI false

noncomputable section

variable {k : Type u} [Field k] {G : AffineAlgebraicGroup k}

private theorem localMaximalSplitTorus {P S : ClosedSubgroup G.val}
    (hS : IsMaximalSplitTorus S) (j : S.group ⟶ P.group)
    (hj : j ≫ P.inclusion = S.inclusion) :
    IsMaximalSplitTorus (restrictSubgroup S P j hj) := by
  let T := restrictSubgroup S P j hj
  refine ⟨hS.1, fun A hA hTA ↦ (subgroupOfSubgroup_le P A T).mp ?_⟩
  have he : subgroupOfSubgroup P T = S := compose_restrict S P j hj
  have hSA : IsSubgroupOf S (subgroupOfSubgroup P A) :=
    he ▸ (subgroupOfSubgroup_le P T A).mpr hTA
  exact he.symm ▸ hS.2 (subgroupOfSubgroup P A) hA hSA

private theorem centralizerInMinimalParabolic (levi : MinimalParabolicLevi.{u})
    {S P C : ClosedSubgroup G.val} (hS : IsMaximalSplitTorus S)
    (hP : IsMinimalParabolic G P) (hSP : IsSubgroupOf S P)
    (hC : RepresentsSubgroup C (fun _ g ↦ Centralizes S.inclusion g)) :
    IsSubgroupOf C P := by
  obtain ⟨j, hj⟩ := hSP
  let T := restrictSubgroup S P j hj
  have he : subgroupOfSubgroup P T = S := compose_restrict S P j hj
  obtain ⟨c, D, hPD, _, _, _, hDC⟩ := levi G P hP T (localMaximalSplitTorus hS j hj)
  have hcentral : Centralizes S.inclusion C.inclusion.hom.hom :=
    (hC _ _).mpr ⟨𝟙 _, Category.id_comp _⟩
  have hcentral' : Centralizes (subgroupOfSubgroup P T).inclusion C.inclusion.hom.hom :=
    he.symm ▸ hcentral
  obtain ⟨x, hx⟩ := (hDC _ _).mp hcentral'
  exact subgroupTrans (factor_group_through_subgroup D.centralizer C.inclusion x hx)
    (subgroupTrans ⟨D.sectionMap, D.section_in_G⟩ hPD.2)

private theorem centralizesOfProjection {S P C : ClosedSubgroup G.val}
    (f : S.group ⟶ P.group) (hf : f ≫ P.inclusion = S.inclusion)
    (p : P.group ⟶ C.group) (i : S.group ⟶ C.group)
    (hi : i ≫ C.inclusion = S.inclusion) (hfi : f ≫ p = i)
    (hC : RepresentsSubgroup C (fun _ g ↦ Centralizes S.inclusion g))
    {Y : SchemeOver k} {g : Y ⟶ G.val.X}
    (hp : FactorsThrough P g) (hn : Normalizes S.inclusion g) :
    Centralizes S.inclusion g := by
  obtain ⟨b, hb⟩ := hp
  change b ≫ P.inclusion.hom.hom = g at hb
  have hj' : f.hom.hom ≫ P.inclusion.hom.hom = S.inclusion.hom.hom :=
    congrArg (fun z : S.group ⟶ G.val ↦ z.hom.hom) hf
  have hfi' : f.hom.hom ≫ p.hom.hom = i.hom.hom :=
    congrArg (fun z : S.group ⟶ C.group ↦ z.hom.hom) hfi
  haveI : Mono P.inclusion.hom.hom := mono_over _ P.isClosedImmersion
  haveI : Mono i.hom.hom := by
    haveI : Mono S.inclusion.hom.hom := mono_over _ S.isClosedImmersion
    exact mono_of_mono_fac (congrArg (fun z : S.group ⟶ G.val ↦ z.hom.hom) hi)
  apply (centralizes_iff S.inclusion g).mpr
  intro U y t
  obtain ⟨s, hs⟩ := ((normalizes_iff_sections S g).mp hn U y t).1
  change s ≫ S.inclusion.hom.hom = (y ≫ g) * (t ≫ S.inclusion.hom.hom) * (y ≫ g)⁻¹ at hs
  have hsp : s ≫ f.hom.hom = (y ≫ b) * (t ≫ f.hom.hom) * (y ≫ b)⁻¹ := by
    apply (cancel_mono P.inclusion.hom.hom).mp
    change s ≫ f.hom.hom ≫ P.inclusion.hom.hom = _ ≫ _
    rw [hj', hs, MonObj.mul_comp, GrpObj.inv_comp, MonObj.mul_comp]
    simp only [Category.assoc, hj', hb]
  let z : U ⟶ C.group.X := y ≫ b ≫ p.hom.hom
  have hc := (hC U (z ≫ C.inclusion.hom.hom)).mpr ⟨z, rfl⟩
  have hz : Commute z (t ≫ i.hom.hom) := by
    have h := (centralizes_iff _ _).mp hc U (𝟙 _) t
    haveI : Mono C.inclusion.hom.hom := mono_over _ C.isClosedImmersion
    apply (cancel_mono C.inclusion.hom.hom).mp
    have hi' : i.hom.hom ≫ C.inclusion.hom.hom = S.inclusion.hom.hom := (Grp.forget _).congr_map hi
    change (z * (t ≫ i.hom.hom)) ≫ C.inclusion.hom.hom =
      ((t ≫ i.hom.hom) * z) ≫ C.inclusion.hom.hom
    rw [MonObj.mul_comp, MonObj.mul_comp, Category.assoc t i.hom.hom C.inclusion.hom.hom, hi']
    simpa only [Category.id_comp, Category.assoc] using h.eq
  have hst : s = t := by
    apply (cancel_mono i.hom.hom).mp
    calc
      s ≫ i.hom.hom = (s ≫ f.hom.hom) ≫ p.hom.hom := by rw [Category.assoc, hfi']
      _ = z * (t ≫ i.hom.hom) * z⁻¹ := by
        rw [hsp, MonObj.mul_comp, MonObj.mul_comp, GrpObj.inv_comp, Category.assoc, Category.assoc,
          hfi']
      _ = t ≫ i.hom.hom := by rw [hz.eq, mul_assoc, mul_inv_cancel, mul_one]
  rw [hst] at hs
  exact mul_inv_eq_iff_eq_mul.mp hs.symm

private theorem centralizesOfParabolicNormalizer (levi : MinimalParabolicLevi.{u})
    {S P : ClosedSubgroup G.val} (hS : IsMaximalSplitTorus S)
    (hP : IsMinimalParabolic G P) (hSP : IsSubgroupOf S P)
    {Y : SchemeOver k} {g : Y ⟶ G.val.X} (hp : FactorsThrough P g)
    (hn : Normalizes S.inclusion g) : Centralizes S.inclusion g := by
  obtain ⟨j, hj⟩ := hSP
  let T := restrictSubgroup S P j hj
  have he : subgroupOfSubgroup P T = S := compose_restrict S P j hj
  obtain ⟨c, D, hPD, _, _, hSC, hDC⟩ := levi G P hP T (localMaximalSplitTorus hS j hj)
  obtain ⟨i, hi⟩ := (show IsSubgroupOf S D.centralizer from he ▸ hSC)
  let f := i ≫ D.sectionMap
  have hf : f ≫ D.parabolic.inclusion = S.inclusion := by
    rw [Category.assoc, D.section_in_G, hi]
  have hfi : f ≫ D.limit = i := by simp [f, Category.assoc, D.section_limit]
  exact centralizesOfProjection f hf D.limit i hi hfi (he ▸ hDC)
    (sections_of_subgroup hPD.1 hp) hn

private theorem normalizerIntersection (levi : MinimalParabolicLevi.{u})
    {S P N C : ClosedSubgroup G.val} (hS : IsMaximalSplitTorus S)
    (hP : IsMinimalParabolic G P) (hSP : IsSubgroupOf S P)
    (hN : RepresentsSubgroup N (fun _ g ↦ Normalizes S.inclusion g))
    (hC : RepresentsSubgroup C (fun _ g ↦ Centralizes S.inclusion g))
    (hCN : IsSubgroupOf C N) : IsSchemeIntersection {N, P} C := by
  have hCP := centralizerInMinimalParabolic levi hS hP hSP hC
  intro Y y
  change FactorsThrough C y ↔ ∀ H ∈ ({N, P} : Set (ClosedSubgroup G.val)), FactorsThrough H y
  constructor
  · intro hc H hH
    rcases Set.mem_insert_iff.mp hH with rfl | he
    · exact sections_of_subgroup hCN hc
    · obtain rfl := Set.mem_singleton_iff.mp he
      exact sections_of_subgroup hCP hc
  · intro h
    exact (hC _ _).mp (centralizesOfParabolicNormalizer levi hS hP hSP
      (h P (by simp)) ((hN _ _).mpr (h N (by simp))))

theorem finiteConstantQuotient : FiniteConstantQuotient.{u} := by
  intro k _ G hG S hS
  obtain ⟨N, C, j, hjc, Q, q, hN, hC, hj, hq, hf, he, _, hs, _⟩ :=
    LinearAlgebraicGroups.NormalizerLatticeAction.quotientByCentralizer
      G hG.1 (connected_of_reductive G hG) S (isTorus_of_split hS.1)
  obtain ⟨D⟩ := hs hS.1
  exact ⟨⟨N, C, j, hjc, Q, q, hN, hC, hj, hq, hf, he, D⟩,
    fun _ hP hSP ↦ normalizerIntersection minimalParabolicLevi hS hP hSP hN hC ⟨j, hj⟩⟩

private theorem conjugatesInclusions {A B C D : ClosedSubgroup G.val}
    {g : 𝟙_ (SchemeOver k) ⟶ G.val.X}
    (hAC : ConjugatesSubgroups g A C) (hBD : ConjugatesSubgroups g B D)
    (hAB : IsSubgroupOf A B) : IsSubgroupOf C D :=
  subgroupTrans
    (conjugates_same_target hAC (conjugates_transport_ambient A g)).1
    (transportSubgroup_le hAB hBD)

private theorem rationalConjugator (conjugateParabolics : MinimalParabolicsConjugate.{u})
    (conjugateTori : MaximalSplitToriConjugateByRadical.{u})
    (levi : MinimalParabolicLevi.{u}) {S A B : ClosedSubgroup G.val}
    (hS : IsMaximalSplitTorus S) (hA : IsMinimalParabolic G A) (hB : IsMinimalParabolic G B)
    (hSA : IsSubgroupOf S A) (hSB : IsSubgroupOf S B) (D : QuotientData S) :
    ∃ n : 𝟙_ (SchemeOver k) ⟶ D.normalizer.group.X,
      ConjugatesSubgroups (n ≫ D.normalizer.inclusion.hom.hom) A B := by
  obtain ⟨g, e, he⟩ := conjugateParabolics G A B hA hB
  obtain ⟨a, ha⟩ := hSA
  obtain ⟨b, hb⟩ := hSB
  let Sₐ := restrictSubgroup S A a ha
  let Sᵦ := restrictSubgroup S B b hb
  let T := transportSubgroup e Sₐ
  have hST : ConjugatesSubgroups g S (subgroupOfSubgroup B T) := by
    rw [← compose_restrict S A a ha]
    exact conjugates_transport e he Sₐ
  have hT : IsMaximalSplitTorus T := by
    -- Conjugation transports maximality in G, then restrict to the target parabolic.
    have hm := maximalSplitOfConjugate hST hS
    refine ⟨hm.1, fun X hX hTX ↦ (subgroupOfSubgroup_le B X T).mp
      (hm.2 (subgroupOfSubgroup B X) hX ((subgroupOfSubgroup_le B T X).mpr hTX))⟩
  have hSb := localMaximalSplitTorus hS b hb
  obtain ⟨c, E, hBE, hrad, _, _, _⟩ := levi G B hB Sᵦ hSb
  obtain ⟨f, _⟩ := subgroupOf_mutual_iso hBE.1 hBE.2
  obtain ⟨u, hu⟩ := conjugateTori G B hB
    (pushSubgroup f.symm (contractingSubgroup E))
    (radical_transport (A := closedSubgroupAlgebraicGroup E.parabolic)
      (B := closedSubgroupAlgebraicGroup B) f.symm _ hrad.1) T Sᵦ hT hSb
  let x := u ≫ (pushSubgroup
    f.symm (contractingSubgroup E)).inclusion.hom.hom
  have hs := conjugates_in_ambient B hu
  have hsame : SameSubgroup (subgroupOfSubgroup B Sᵦ) S := by
    rw [compose_restrict S B b hb]
    exact ⟨⟨𝟙 _, Category.id_comp _⟩, ⟨𝟙 _, Category.id_comp _⟩⟩
  have hnorm := normalizes_of_conjugates_self S (conjugates_trans hST (conjugates_of_same hs hsame))
  obtain ⟨n, hn⟩ := (D.normalizerProperty _ _).mp hnorm
  exact ⟨n, hn.symm ▸ conjugates_trans (show ConjugatesSubgroups g A B from ⟨e, he⟩)
    (conjugates_preserves_borel B x)⟩

private theorem sameOfConjugateInclusion {A B : ClosedSubgroup G.val}
    {g : 𝟙_ (SchemeOver k) ⟶ G.val.X} (hg : ConjugatesSubgroups g A B)
    (hAB : IsSubgroupOf A B) : SameSubgroup A B := by
  letI := G.property.1
  letI := G.property.2.1
  letI : IsLocallyNoetherian G.val.X.left := LocallyOfFiniteType.isLocallyNoetherian G.val.X.hom
  letI : IsNoetherianRing Γ(G.val.X.left, ⊤) :=
    IsLocallyNoetherian.component_noetherian ⟨⊤, isAffineOpen_top _⟩
  let ideals : Set (Ideal Γ(G.val.X.left, ⊤)) :=
    {I | ∃ (C : ClosedSubgroup G.val) (c : 𝟙_ (SchemeOver k) ⟶ G.val.X),
      ConjugatesSubgroups c B C ∧ definingIdeal C = I}
  obtain ⟨_, ⟨C, c, hc, rfl⟩, hmax⟩ := wellFounded_gt.has_min ideals
    ⟨definingIdeal (transportSubgroup (conjugationIso g) B), _, g,
      conjugates_transport_ambient B g, rfl⟩
  let A' := transportSubgroup (conjugationIso c) A
  have ha := conjugates_transport_ambient A c
  have hA'C := conjugatesInclusions ha hc hAB
  obtain ⟨f, hf⟩ := hA'C
  have heq : definingIdeal A' = definingIdeal C := by
    by_contra hne
    exact hmax (definingIdeal A') ⟨A', c * g⁻¹, conjugates_trans (conjugates_inverse hg) ha, rfl⟩
      (lt_of_le_of_ne (definingIdeal_le f hf) (Ne.symm hne))
  haveI := factor_iso_of_definingIdeal_eq f hf heq
  exact ⟨hAB, conjugatesInclusions (conjugates_inverse hc) (conjugates_inverse ha)
    ⟨inv f, by rw [← hf, IsIso.inv_hom_id_assoc]⟩⟩

private theorem minimalSubparabolic (A : ClosedSubgroup G.val) (hA : IsParabolic G A) :
    ∃ B : ClosedSubgroup G.val, IsMinimalParabolic G B ∧ IsSubgroupOf B A := by
  letI := G.property.1
  letI := G.property.2.1
  letI : IsLocallyNoetherian G.val.X.left := LocallyOfFiniteType.isLocallyNoetherian G.val.X.hom
  letI : IsNoetherianRing Γ(G.val.X.left, ⊤) :=
    IsLocallyNoetherian.component_noetherian ⟨⊤, isAffineOpen_top _⟩
  let ideals : Set (Ideal Γ(G.val.X.left, ⊤)) :=
    {I | ∃ B : ClosedSubgroup G.val, IsParabolic G B ∧ IsSubgroupOf B A ∧ definingIdeal B = I}
  obtain ⟨_, ⟨B, hB, hBA, rfl⟩, hmax⟩ := wellFounded_gt.has_min ideals
    ⟨definingIdeal A, A, hA, ⟨𝟙 _, Category.id_comp _⟩, rfl⟩
  refine ⟨B, ⟨hB, ?_⟩, hBA⟩
  intro C hC hCB
  obtain ⟨f, hf⟩ := hCB
  have heq : definingIdeal C = definingIdeal B := by
    by_contra hne
    exact hmax (definingIdeal C) ⟨C, hC, subgroupTrans ⟨f, hf⟩ hBA, rfl⟩
      (lt_of_le_of_ne (definingIdeal_le f hf) (Ne.symm hne))
  haveI := factor_iso_of_definingIdeal_eq f hf heq
  exact ⟨inv f, by rw [← hf, IsIso.inv_hom_id_assoc]⟩

private theorem minimalOfGeometricallyConjugate {A B : ClosedSubgroup G.val}
    (hA : IsMinimalParabolic G A) (hB : IsParabolic G B)
    (g : 𝟙_ (SchemeOver (AlgebraicClosure k)) ⟶ (GeometricGroup G).val.X)
    (hg : ConjugatesSubgroups g (extendSubgroup (AlgebraicClosure k) A)
      (extendSubgroup (AlgebraicClosure k) B)) : IsMinimalParabolic G B := by
  let K := AlgebraicClosure k
  obtain ⟨C, hC, hCB⟩ := minimalSubparabolic B hB
  obtain ⟨x, hx⟩ := minimalParabolicsConjugate G C A hC hA
  have hc := conjugates_trans (conjugates_extend K hx) hg
  have h' := sameOfConjugateInclusion (G := GeometricGroup G) hc (subgroup_extend K hCB)
  have hBC : IsSubgroupOf B C := subgroup_descend K h'.2
  exact ⟨hB, fun D hD hDB ↦ subgroupTrans hBC (hC.2 D hD (subgroupTrans hDB hBC))⟩

open scoped CategoryTheory.Obj in
private theorem conjugateFamilyOfGeometricLabel {S : ClosedSubgroup G.val}
    (D : QuotientData S) (w : D.splitImage.labels) (K : Type u) [Field K] [Algebra k K]
    (n : 𝟙_ (SchemeOver K) ⟶ ((groupBaseChange k K).obj D.normalizer.group).X)
    (hn : n ≫ ((groupBaseChange k K).map D.projection).hom.hom =
      scalarExtendedRationalPoint K (D.splitImage.constantGroup.sectionPoint w)) :
    conjugateFamily ((groupBaseChange k K).map S.inclusion)
      (n ≫ (baseChange k K).map D.normalizer.inclusion.hom.hom) =
      fst ((baseChange k K).obj S.group.X) (𝟙_ (SchemeOver K)) ≫
      (baseChange k K).map ((D.splitImage.conjugation w).hom ≫ S.inclusion).hom.hom := by
  let F := baseChange k K
  let E := groupBaseChange k K
  let U := 𝟙_ (SchemeOver K)
  let adj := extensionAdj (k := k) K
  let n₀ := (adj.homEquiv U D.normalizer.group.X).symm n
  let g := n ≫ F.map D.normalizer.inclusion.hom.hom
  let g₀ := (adj.homEquiv U G.val.X).symm g
  let v := D.splitImage.constantGroup.sectionPoint w
  have h₀ : n₀ ≫ D.projection.hom.hom = toUnit _ ≫ v := by
    rw [← adj.homEquiv_naturality_right_symm]
    change (adj.homEquiv U D.group.val.X).symm (n ≫ F.map D.projection.hom.hom) = _
    have hv : n ≫ F.map D.projection.hom.hom = scalarExtendedRationalPoint K v := hn
    rw [hv, scalarExtendedRationalPoint, adj.homEquiv_naturality_right_symm]
    exact congrArg (· ≫ v) (Subsingleton.elim _ _)
  have hg₀ : g₀ = n₀ ≫ D.normalizer.inclusion.hom.hom :=
    adj.homEquiv_naturality_right_symm n D.normalizer.inclusion.hom.hom
  let i := S.inclusion
  let a := (D.splitImage.conjugation w).hom ≫ i
  have he := D.splitImage.conjugates _ n₀ w h₀
  have hgeom : conjugateFamily (E.map i) g = fst (F.obj S.group.X) U ≫ F.map a.hom.hom := by
    let L := Over.map (fieldSpecMap k K)
    let b := lift (L.map (fst (F.obj S.group.X) U) ≫ adj.counit.app S.group.X)
      (L.map (snd (F.obj S.group.X) U))
    let q := fst S.group.X G.val.X ≫ a.hom.hom
    have hg : conjugateFamily (E.map i) g =
        (F.obj S.group.X ◁ g) ≫ (prodComparisonIso F S.group.X G.val.X).inv ≫ F.map (conjugation i) := by
      rw [conjugation_baseChange K i]
      exact (whisker_conjugation (E.map i) g).symm
    have hq : (prodComparisonIso F S.group.X G.val.X).inv ≫ F.map q =
        fst (F.obj S.group.X) (F.obj G.val.X) ≫ F.map a.hom.hom := by
      rw [Functor.map_comp, ← Category.assoc, prodComparison_inv_fst]
    rw [hg, ← whiskerLeft_fst_assoc (F.obj S.group.X) g, ← hq]
    apply (adj.homEquiv (F.obj S.group.X ⊗ U) G.val.X).symm.injective
    erw [adjoint_family K (conjugation i) g, adjoint_family K q g]
    change b ≫ (S.group.X ◁ g₀) ≫ conjugation i = b ≫ (S.group.X ◁ g₀) ≫ q
    simp only [whisker_conjugation, q, whiskerLeft_fst_assoc]
    rw [hg₀]
    exact congrArg (fun x ↦ b ≫ x) he
  exact hgeom

private theorem conjugationOfRationalFamily {A B : GroupScheme k} (i : A ⟶ B)
    (g : 𝟙_ (SchemeOver k) ⟶ B.X) {t : A.X ⟶ B.X}
    (h : conjugateFamily i g = fst A.X (𝟙_ (SchemeOver k)) ≫ t) :
    t = (i ≫ (conjugationIso g).hom).hom.hom := by
  let l : A.X ⟶ A.X ⊗ (𝟙_ (SchemeOver k)) := lift (𝟙 _) (toUnit _)
  have hc : l ≫ conjugateFamily i g = conjugate g i.hom.hom := by
    rw [comp_conjugateFamily]
    simp only [l, lift_fst_assoc, lift_snd_assoc, Category.id_comp, conjugate]
  have ht : l ≫ conjugateFamily i g = t := by
    rw [h, ← Category.assoc, show l ≫ fst _ _ = 𝟙 _ from lift_fst _ _, Category.id_comp]
  have hi : (i ≫ (conjugationIso g).hom).hom.hom = conjugate g i.hom.hom := by
    change i.hom.hom ≫ conjugate g (𝟙 _) = _
    rw [comp_conjugate, Category.comp_id]
  exact ht.symm.trans (hc.trans hi.symm)

open scoped CategoryTheory.Obj in
private theorem conjugatesSplitTorusOfGeometricLabel {S : ClosedSubgroup G.val}
    (D : QuotientData S) (w : D.splitImage.labels) (K : Type u) [Field K] [Algebra k K]
    (n : 𝟙_ (SchemeOver K) ⟶ ((groupBaseChange k K).obj D.normalizer.group).X)
    (hn : n ≫ ((groupBaseChange k K).map D.projection).hom.hom =
      scalarExtendedRationalPoint K (D.splitImage.constantGroup.sectionPoint w)) :
    ((groupBaseChange k K).map (D.splitImage.conjugation w).hom) ≫
      (extendSubgroup K S).inclusion =
    (extendSubgroup K S).inclusion ≫
      (conjugationIso (n ≫ (extendSubgroup K D.normalizer).inclusion.hom.hom)).hom := by
  let E := groupBaseChange k K
  let i := E.map S.inclusion
  let g := n ≫ (extendSubgroup K D.normalizer).inclusion.hom.hom
  change E.map (D.splitImage.conjugation w).hom ≫ i = i ≫ (conjugationIso g).hom
  rw [← E.map_comp]
  apply Grp.hom_ext
  exact conjugationOfRationalFamily i g (conjugateFamilyOfGeometricLabel D w K n hn)

private theorem conjugatesFromSame {A B C : ClosedSubgroup G.val}
    {g : 𝟙_ (SchemeOver k) ⟶ G.val.X} (hAB : SameSubgroup A B)
    (h : ConjugatesSubgroups g B C) : ConjugatesSubgroups g A C := by
  have h' := conjugates_inverse (conjugates_of_same (conjugates_inverse h) ⟨hAB.2, hAB.1⟩)
  simpa only [inv_inv] using h'

private theorem projectionOfParabolicFactor {S P : ClosedSubgroup G.val}
    (D : QuotientData S) (hS : IsMaximalSplitTorus S) (hP : IsMinimalParabolic G P)
    (hSP : IsSubgroupOf S P) {Y : SchemeOver k} (n : Y ⟶ D.normalizer.group.X)
    (hn : FactorsThrough P (n ≫ D.normalizer.inclusion.hom.hom)) :
    n ≫ D.projection.hom.hom = 1 := by
  have hI := normalizerIntersection minimalParabolicLevi hS hP hSP
    D.normalizerProperty D.centralizerProperty ⟨D.inclusion, D.inclusionProperty⟩
  obtain ⟨a, ha⟩ := (hI _ _).mpr (by
    intro B hB
    rcases Set.mem_insert_iff.mp hB with rfl | hb
    · exact ⟨n, rfl⟩
    · obtain rfl := Set.mem_singleton_iff.mp hb
      exact hn)
  haveI : Mono D.normalizer.inclusion.hom.hom := mono_over _ D.normalizer.isClosedImmersion
  have h : a ≫ D.inclusion.hom.hom = n := by
    apply (cancel_mono D.normalizer.inclusion.hom.hom).mp
    rw [Category.assoc, ← show (D.inclusion ≫ D.normalizer.inclusion).hom.hom =
      D.inclusion.hom.hom ≫ D.normalizer.inclusion.hom.hom from rfl, D.inclusionProperty]
    exact ha
  exact (schemeKernel_sections D.quotientProperty.1 n).mp ⟨a, h⟩

private theorem geometricProjectionOfParabolicFactor {S P : ClosedSubgroup G.val}
    (D : QuotientData S) (hS : IsMaximalSplitTorus S) (hP : IsMinimalParabolic G P)
    (hSP : IsSubgroupOf S P) (K : Type u) [Field K] [Algebra k K]
    {Y : SchemeOver K} (n : Y ⟶ (extendSubgroup K D.normalizer).group.X)
    (hn : FactorsThrough (extendSubgroup K P)
      (n ≫ (extendSubgroup K D.normalizer).inclusion.hom.hom)) :
    n ≫ ((groupBaseChange k K).map D.projection).hom.hom = 1 := by
  let F := baseChange k K
  let adj := extensionAdj (k := k) K
  let b := (adj.homEquiv Y D.normalizer.group.X).symm n
  have h : FactorsThrough P (b ≫ D.normalizer.inclusion.hom.hom) := by
    change ∃ z, z ≫ P.inclusion.hom.hom = b ≫ D.normalizer.inclusion.hom.hom
    dsimp only [b]
    rw [← adj.homEquiv_naturality_right_symm]
    exact (adjoint_factorization K P.inclusion.hom.hom _).mp hn
  have hb := projectionOfParabolicFactor D hS hP hSP b h
  apply (adj.homEquiv Y D.group.val.X).symm.injective
  change (adj.homEquiv Y D.group.val.X).symm (n ≫ F.map D.projection.hom.hom) =
    (adj.homEquiv Y D.group.val.X).symm
      (toUnit Y ≫ (Functor.LaxMonoidal.ε F ≫ F.map η[D.group.val.X]))
  rw [← Category.assoc (toUnit Y), adj.homEquiv_naturality_right_symm, adj.homEquiv_naturality_right_symm]
  exact hb.trans (congrArg (· ≫ η[D.group.val.X]) (Subsingleton.elim _ _))

private theorem parabolicOfGeometricLabel {S P : ClosedSubgroup G.val}
    (hG : IsReductive G) (hS : IsMaximalSplitTorus S) (hP : IsMinimalParabolic G P)
    (hSP : IsSubgroupOf S P) (D : QuotientData S) (w : D.splitImage.labels)
    (n : 𝟙_ (SchemeOver (AlgebraicClosure k)) ⟶
      (extendSubgroup (AlgebraicClosure k) D.normalizer).group.X)
    (hn : n ≫ ((groupBaseChange k (AlgebraicClosure k)).map D.projection).hom.hom =
      scalarExtendedRationalPoint (AlgebraicClosure k) (D.splitImage.constantGroup.sectionPoint w)) :
    ∃ Q : ClosedSubgroup G.val, IsMinimalParabolic G Q ∧ IsSubgroupOf S Q ∧
      ConjugatesSubgroups (n ≫ (extendSubgroup (AlgebraicClosure k) D.normalizer).inclusion.hom.hom)
        (extendSubgroup (AlgebraicClosure k) P) (extendSubgroup (AlgebraicClosure k) Q) := by
  letI : Smooth G.val.X.hom := hG.1
  letI : ConnectedSpace G.val.X.left := connected_of_reductive G hG
  obtain ⟨a, ha⟩ := hSP
  let T := restrictSubgroup S P a ha
  obtain ⟨c, L, hPL, _, _, _, _⟩ := minimalParabolicLevi G P hP T
    (localMaximalSplitTorus hS a ha)
  let i : S.group ⟶ G.val := (subgroupOfSubgroup P T).inclusion
  let c₀ : Cocharacter S.group := c
  have hi : i = S.inclusion := ha
  let e := D.splitImage.conjugation w
  let b : Cocharacter G.val := (c₀ ≫ e.hom) ≫ i
  obtain ⟨M⟩ := existsLimitDecomposition G b
  have hMS : IsSubgroupOf S M.parabolic :=
    torus_in_limit_parabolic S hS.1 M ⟨c₀ ≫ e.hom, congrArg ((c₀ ≫ e.hom) ≫ ·) hi.symm⟩
  let K := AlgebraicClosure k
  let F := groupBaseChange k K
  let g := n ≫ (extendSubgroup K D.normalizer).inclusion.hom.hom
  have hlabel : F.map e.hom ≫ F.map i = F.map i ≫ (conjugationIso g).hom := by
    rw [hi]
    exact conjugatesSplitTorusOfGeometricLabel D w K n hn
  obtain ⟨d, hd⟩ := gm_baseChange k K
  obtain ⟨L'⟩ := existsLimitDecomposition (GeometricGroup G) (d.hom ≫ F.map (c₀ ≫ i))
  obtain ⟨M'⟩ := existsLimitDecomposition (GeometricGroup G) (d.hom ≫ F.map b)
  have hdyn : (d.hom ≫ F.map (c₀ ≫ i)) ≫ (conjugationIso g).hom = d.hom ≫ F.map b := by
    simp only [b, Functor.map_comp, Category.assoc, ← hlabel]
  let E := hdyn.symm ▸ M'
  have hE : E.parabolic = M'.parabolic := limitParabolic_transport hdyn.symm M'
  have hsame := pushLimitParabolic (GeometricGroup G) (GeometricGroup G) (conjugationIso g) L' E
  rw [hE] at hsame
  have hc : ConjugatesSubgroups g L'.parabolic M'.parabolic :=
    conjugates_of_same (conjugates_transport_ambient L'.parabolic g) hsame
  have hL' := (limits_subgroups_extend G L d hd L').1
  have hM' := (limits_subgroups_extend G M d hd M').1
  have hP' : SameSubgroup (extendSubgroup K P) L'.parabolic :=
    ⟨subgroupTrans (subgroup_extend K hPL.1) hL'.2,
      subgroupTrans hL'.1 (subgroup_extend K hPL.2)⟩
  have hgeom : ConjugatesSubgroups g (extendSubgroup K P) (extendSubgroup K M.parabolic) :=
    conjugatesFromSame hP' (conjugates_of_same hc hM')
  have hMP := minimalOfGeometricallyConjugate hP (limitIsParabolic G hG b M) g hgeom
  exact ⟨M.parabolic, hMP, hMS, hgeom⟩

private theorem geometricConjugatorsProjectEqually {S P Q : ClosedSubgroup G.val}
    (D : QuotientData S) (hS : IsMaximalSplitTorus S)
    (hP : IsMinimalParabolic G P) (hSP : IsSubgroupOf S P)
    (K : Type u) [Field K] [Algebra k K]
    {m n : 𝟙_ (SchemeOver K) ⟶ (extendSubgroup K D.normalizer).group.X}
    (hm : ConjugatesSubgroups (m ≫ (extendSubgroup K D.normalizer).inclusion.hom.hom)
      (extendSubgroup K P) (extendSubgroup K Q))
    (hn : ConjugatesSubgroups (n ≫ (extendSubgroup K D.normalizer).inclusion.hom.hom)
      (extendSubgroup K P) (extendSubgroup K Q)) :
    m ≫ ((groupBaseChange k K).map D.projection).hom.hom =
      n ≫ ((groupBaseChange k K).map D.projection).hom.hom := by
  let j := IsMonHom.monoidHom (extendSubgroup K D.normalizer).inclusion.hom.hom (𝟙_ (SchemeOver K))
  have hx : ConjugatesSubgroups (j (m⁻¹ * n)) (extendSubgroup K P) (extendSubgroup K P) := by
    rw [map_mul, map_inv]
    exact conjugates_trans hn (conjugates_inverse hm)
  obtain ⟨_, hPK⟩ := normalizerSchemeBaseChange k K P.inclusion P P.isClosedImmersion
    (Flag.StandardParabolics.groundFieldParabolicNormalizer G P hP.1)
  have hxP : FactorsThrough (extendSubgroup K P) (j (m⁻¹ * n)) :=
    (hPK _ _).mp (normalizes_of_conjugates_self _ hx)
  let π := IsMonHom.monoidHom ((groupBaseChange k K).map D.projection).hom.hom (𝟙_ (SchemeOver K))
  have hπ : π (m⁻¹ * n) = 1 := geometricProjectionOfParabolicFactor D hS hP hSP K (m⁻¹ * n) hxP
  change π m = π n
  simpa only [map_mul, map_inv, inv_mul_eq_one] using hπ

private theorem labelHasRationalRepresentative {S P : ClosedSubgroup G.val}
    (hG : IsReductive G) (hS : IsMaximalSplitTorus S) (hP : IsMinimalParabolic G P)
    (hSP : IsSubgroupOf S P) (D : QuotientData S) (w : D.splitImage.labels) :
    ∃ n, rationalProjection D n = D.splitImage.constantGroup.sectionPoint w := by
  let K := AlgebraicClosure k
  let v := D.splitImage.constantGroup.sectionPoint w
  obtain ⟨n, hn, _⟩ := geometricFibres_of_fppf
    (C := closedSubgroupAlgebraicGroup D.centralizer)
    (N := closedSubgroupAlgebraicGroup D.normalizer) D.projection D.inclusion D.inclusionClosed
    D.quotientProperty K (scalarExtendedRationalPoint K v)
  obtain ⟨Q, hQ, hSQ, hgeom⟩ := parabolicOfGeometricLabel hG hS hP hSP D w n hn
  obtain ⟨m, hm⟩ := rationalConjugator minimalParabolicsConjugate maximalSplitToriConjugateByRadical
    minimalParabolicLevi hS hP hQ hSP hSQ D
  let m' : 𝟙_ (SchemeOver K) ⟶ (extendSubgroup K D.normalizer).group.X := scalarExtendedRationalPoint K m
  let j := (extendSubgroup K D.normalizer).inclusion.hom.hom
  have hm' : ConjugatesSubgroups (m' ≫ j) (extendSubgroup K P) (extendSubgroup K Q) := by
    have h : scalarExtendedRationalPoint K (m ≫ D.normalizer.inclusion.hom.hom) = m' ≫ j :=
      scalarExtendedPoint_natural K m D.normalizer.inclusion.hom.hom
    rw [← h]
    exact conjugates_extend K hm
  have hπ := geometricConjugatorsProjectEqually D hS hP hSP K hm' hgeom
  refine ⟨m, scalarExtended_point_injective K _ ?_⟩
  exact (scalarExtendedPoint_natural K m D.projection.hom.hom).trans (hπ.trans hn)

private def constantRationalEquiv {Q : GroupScheme k} {W : Type u} [Group W]
    (C : ConstantGroup Q W) : W ≃* (𝟙_ (SchemeOver k) ⟶ Q.X) := by
  let U := 𝟙_ (SchemeOver k)
  let e : (Over.mk (𝟙 (Spec (CommRingCat.of k))) : SchemeOver k) ≅ U :=
    Over.mkIdTerminal.uniqueUpToIso isTerminalTensorUnit
  let x := e.hom.left (IsLocalRing.closedPoint k)
  letI : Subsingleton U.left :=
    ((Over.forget (Spec (CommRingCat.of k))).mapIso e).hom.homeomorph.subsingleton_congr.mp
      (inferInstanceAs (Subsingleton (Spec (CommRingCat.of k))))
  have h (w : W) : C.families U (C.sectionPoint w) = LocallyConstant.const U.left w := by
    simpa only [toUnit_unique (toUnit U) (𝟙 U), Category.id_comp] using C.constant U w
  apply MulEquiv.ofBijective C.sectionPoint
  constructor
  · intro a b hab
    have h' := congrArg (fun t ↦ C.families U t x) hab
    rw [h a, h b] at h'
    exact h'
  · intro y
    refine ⟨C.families U y x, (C.families U).injective ?_⟩
    rw [h]
    apply LocallyConstant.ext
    intro z
    rw [Subsingleton.elim z x]
    rfl

private abbrev normalizerPoint {S : ClosedSubgroup G.val} (D : QuotientData S) :=
  IsMonHom.monoidHom D.normalizer.inclusion.hom.hom (𝟙_ (SchemeOver k))

private abbrev MinimalThrough (S : ClosedSubgroup G.val) :=
  {P : ClosedSubgroup G.val // IsMinimalParabolic G P ∧ IsSubgroupOf S P}

private abbrev parabolicClass {S : ClosedSubgroup G.val} (x : MinimalThrough S) :
    ParabolicsThrough G S := markedParabolic x.val x.property.1 x.property.2

private def conjugateParabolic {S : ClosedSubgroup G.val} (D : QuotientData S)
    (n : 𝟙_ (SchemeOver k) ⟶ D.normalizer.group.X) (A : MinimalThrough S) : MinimalThrough S := by
  let g := normalizerPoint D n
  let B := transportSubgroup (conjugationIso g) A.val
  have hc : ConjugatesSubgroups g A.val B := conjugates_transport_ambient A.val g
  have hs : ConjugatesSubgroups g S S := conjugates_of_normalizes S
    ((D.normalizerProperty _ _).mpr ⟨n, rfl⟩)
  exact ⟨B, minimalParabolicTransport A.property.1 (conjugationIso g),
    conjugatesInclusions hs hc A.property.2⟩

private theorem conjugateParabolic_spec {S : ClosedSubgroup G.val} (D : QuotientData S)
    (n : 𝟙_ (SchemeOver k) ⟶ D.normalizer.group.X) (A : MinimalThrough S) :
    ConjugatesSubgroups (normalizerPoint D n) A.val (conjugateParabolic D n A).val :=
  conjugates_transport_ambient _ _

private def conjugateParabolicClass {S : ClosedSubgroup G.val} (D : QuotientData S)
    (n : 𝟙_ (SchemeOver k) ⟶ D.normalizer.group.X) :
    ParabolicsThrough G S → ParabolicsThrough G S :=
  Quotient.lift (fun A ↦ parabolicClass (conjugateParabolic D n A)) (fun A B h ↦
    Quotient.sound ⟨conjugatesInclusions (conjugateParabolic_spec D n A)
      (conjugateParabolic_spec D n B) h.1, conjugatesInclusions (conjugateParabolic_spec D n B)
      (conjugateParabolic_spec D n A) h.2⟩)

private theorem conjugateParabolicClass_spec {S : ClosedSubgroup G.val} (D : QuotientData S)
    (n : 𝟙_ (SchemeOver k) ⟶ D.normalizer.group.X) (A B : MinimalThrough S) :
    conjugateParabolicClass D n (parabolicClass A) = parabolicClass B ↔
      ConjugatesSubgroups (normalizerPoint D n) A.val B.val := by
  change parabolicClass (conjugateParabolic D n A) = parabolicClass B ↔ _
  exact ⟨fun h ↦ conjugates_of_same (conjugateParabolic_spec D n A) (Quotient.exact h),
    fun h ↦ Quotient.sound (conjugates_same_target (conjugateParabolic_spec D n A) h)⟩

private theorem conjugateParabolicClass_one {S : ClosedSubgroup G.val} (D : QuotientData S)
    (x : ParabolicsThrough G S) : conjugateParabolicClass D 1 x = x := by
  refine Quotient.inductionOn x fun A ↦ (conjugateParabolicClass_spec D 1 A A).mpr ?_
  have h := conjugates_preserves_borel A.val (1 : 𝟙_ (SchemeOver k) ⟶ A.val.group.X)
  rw [MonObj.one_comp] at h
  simpa only [map_one] using h

private theorem conjugateParabolicClass_mul {S : ClosedSubgroup G.val} (D : QuotientData S)
    (n m : 𝟙_ (SchemeOver k) ⟶ D.normalizer.group.X) (x : ParabolicsThrough G S) :
    conjugateParabolicClass D (n * m) x = conjugateParabolicClass D n (conjugateParabolicClass D m x) := by
  refine Quotient.inductionOn x fun A ↦ (conjugateParabolicClass_spec D (n * m) A
    (conjugateParabolic D n (conjugateParabolic D m A))).mpr ?_
  rw [map_mul]
  exact conjugates_trans (conjugateParabolic_spec D m A)
    (conjugateParabolic_spec D n (conjugateParabolic D m A))

private theorem projection_eq_iff_conjugateClass_eq {S : ClosedSubgroup G.val}
    (D : QuotientData S) (hS : IsMaximalSplitTorus S)
    (n m : 𝟙_ (SchemeOver k) ⟶ D.normalizer.group.X) (x : ParabolicsThrough G S) :
    rationalProjection D n = rationalProjection D m ↔
      conjugateParabolicClass D n x = conjugateParabolicClass D m x := by
  refine Quotient.inductionOn x fun A ↦ ?_
  let B := conjugateParabolic D m A
  change rationalProjection D n = rationalProjection D m ↔
    conjugateParabolicClass D n (parabolicClass A) = parabolicClass B
  rw [conjugateParabolicClass_spec]
  have hm := conjugateParabolic_spec D m A
  let d := m⁻¹ * n
  have hn (h : rationalProjection D n = rationalProjection D m) : rationalProjection D d = 1 := by
    simp only [d, map_mul, map_inv, h, inv_mul_cancel]
  constructor
  · intro h
    have hd : d ≫ D.projection.hom.hom = 1 := hn h
    obtain ⟨a, ha⟩ := (schemeKernel_sections D.quotientProperty.1 d).mpr hd
    change a ≫ D.inclusion.hom.hom = d at ha
    have hC : IsSubgroupOf D.centralizer A.val :=
      centralizerInMinimalParabolic minimalParabolicLevi hS A.property.1 A.property.2 D.centralizerProperty
    have hp : FactorsThrough A.val (normalizerPoint D d) := by
      apply sections_of_subgroup hC
      refine ⟨a, ?_⟩
      change a ≫ D.centralizer.inclusion.hom.hom = d ≫ D.normalizer.inclusion.hom.hom
      rw [← D.inclusionProperty]
      change a ≫ D.inclusion.hom.hom ≫ D.normalizer.inclusion.hom.hom = _
      rw [← Category.assoc, ha]
    have hc := conjugates_of_normalizes A.val (subgroup_normalizes _ hp)
    have ht := conjugates_trans hc hm
    rw [← map_mul, show m * d = n by simp [d]] at ht
    exact ht
  · intro h
    have hc := conjugates_trans h (conjugates_inverse hm)
    rw [← map_inv, ← map_mul] at hc
    have hp : FactorsThrough A.val (normalizerPoint D d) :=
      (Flag.StandardParabolics.groundFieldParabolicNormalizer G A.val A.property.1.1 _ _).mp
        (normalizes_of_conjugates_self _ hc)
    have h' : rationalProjection D d = 1 :=
      projectionOfParabolicFactor D hS A.property.1 A.property.2 d hp
    have h'' : rationalProjection D m = rationalProjection D n := by
      simpa only [d, map_mul, map_inv, inv_mul_eq_one] using h'
    exact h''.symm

/-- The finite constant quotient acts simply transitively, with every label
represented by a rational normalizer point. -/
theorem relativeWeylAction : RelativeWeylAction.{u} := by
  intro k _ G hG S P hS hP hSP D
  classical
  let W := D.splitImage.labels
  let Z := MonoidHom.range (IsMonHom.monoidHom D.inclusion.hom.hom (𝟙_ (SchemeOver k)))
  let C := constantRationalEquiv D.splitImage.constantGroup
  let l := C.symm.toMonoidHom.comp (rationalProjection D)
  have hl (n : 𝟙_ (SchemeOver k) ⟶ D.normalizer.group.X) : C (l n) = rationalProjection D n :=
    C.apply_symm_apply _
  have hC (w : W) : C w = D.splitImage.constantGroup.sectionPoint w := rfl
  have hsurj : Function.Surjective l := by
    intro w
    obtain ⟨n, hn⟩ := labelHasRationalRepresentative hG hS hP hSP D w
    exact ⟨n, C.injective ((hl n).trans (hn.trans (hC w).symm))⟩
  have hker : l.ker = Z := by
    ext n
    change l n = 1 ↔ ∃ a : 𝟙_ (SchemeOver k) ⟶ D.centralizer.group.X, a ≫ D.inclusion.hom.hom = n
    have h := schemeKernel_sections D.quotientProperty.1 n
    constructor
    · intro hn
      apply h.mpr
      change rationalProjection D n = 1
      rw [← hl, hn, map_one]
    · intro hn
      apply C.injective
      rw [hl, map_one]
      exact h.mp hn
  have hZ : Z.Normal := hker ▸ inferInstanceAs (l.ker.Normal)
  let e := (QuotientGroup.quotientMulEquivOfEq hker.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective l hsurj)
  have he (n : 𝟙_ (SchemeOver k) ⟶ D.normalizer.group.X) : e (QuotientGroup.mk n) = l n := by
    change QuotientGroup.quotientKerEquivOfSurjective l hsurj
      (QuotientGroup.quotientMulEquivOfEq hker.symm (QuotientGroup.mk n)) = _
    rw [QuotientGroup.quotientMulEquivOfEq_mk]
    rfl
  obtain ⟨r, hr⟩ := hsurj.hasRightInverse
  let act (w : W) (x : ParabolicsThrough G S) := conjugateParabolicClass D (r w) x
  have hact (n : 𝟙_ (SchemeOver k) ⟶ D.normalizer.group.X) (x : ParabolicsThrough G S) :
      act (l n) x = conjugateParabolicClass D n x := by
    apply (projection_eq_iff_conjugateClass_eq D hS _ _ x).mp
    rw [← hl (r (l n)), hr (l n), hl]
  let a : MulAction W (ParabolicsThrough G S) :=
    { smul := act
      one_smul := fun x ↦ by
        change act 1 x = x
        rw [← l.map_one, hact, conjugateParabolicClass_one]
      mul_smul := fun w v x ↦ by
        change act (w * v) x = act w (act v x)
        rw [← hr w, ← hr v, ← map_mul, hact, hact, hact, conjugateParabolicClass_mul] }
  refine ⟨hZ, e, a, fun n ↦ ?_, labelHasRationalRepresentative hG hS hP hSP D, ?_, ?_⟩
  · rw [he, ← hC, hl]
  · intro n A B hA hB hSA hSB
    change ConjugatesSubgroups (normalizerPoint D n) A B ↔
      act (e (QuotientGroup.mk n)) (parabolicClass ⟨A, hA, hSA⟩) = parabolicClass ⟨B, hB, hSB⟩
    rw [he, hact]
    exact (conjugateParabolicClass_spec D n ⟨A, hA, hSA⟩ ⟨B, hB, hSB⟩).symm
  · intro x y
    refine Quotient.inductionOn₂ x y fun A B ↦ ?_
    obtain ⟨n, hn⟩ := rationalConjugator minimalParabolicsConjugate maximalSplitToriConjugateByRadical
      minimalParabolicLevi hS A.property.1 B.property.1 A.property.2 B.property.2 D
    have h := (conjugateParabolicClass_spec D n A B).mpr hn
    change ∃! w : W, act w (parabolicClass A) = parabolicClass B
    refine ⟨l n, (hact n _).trans h, fun w hw ↦ ?_⟩
    have hpr := (projection_eq_iff_conjugateClass_eq D hS (r w) n (parabolicClass A)).mpr
      (hw.trans h.symm)
    apply C.injective
    rw [hl, ← hr w, hl]
    exact hpr

private theorem commonGeometricallyMaximalTorus {P Q : ClosedSubgroup G.val}
    (hP : IsParabolic G P) (hQ : IsParabolic G Q) :
    ∃ T : ClosedSubgroup G.val, IsTorus T.group ∧
      IsMaximalTorus (extendSubgroup (AlgebraicClosure k) T) ∧ IsSubgroupOf T P ∧ IsSubgroupOf T Q := by
  obtain ⟨_, H, hH, hHs, hHc, _, A, hA, a, ha⟩ := ParabolicIntersection.intersectionGeometry G P Q hP hQ
  let K := AlgebraicClosure k
  let H₀ := closedSubgroupAlgebraicGroup H
  let H' := extendSubgroup K H
  let A' := restrictSubgroup A H' a ha
  have hA' : IsMaximalTorus A' := local_maximal_of_ambient H' A' (by
    rwa [compose_restrict A H' a ha])
  obtain ⟨B, hB, _, hB'⟩ := MaximalToriExist.geometricallyMaximalTorusExists H₀ hHs
    (connected_of_geometricallyConnected hHc)
  let B' := extendSubgroup K B
  have hH's : Smooth (GeometricGroup H₀).val.X.hom := MorphismProperty.pullback_snd _ _ hHs
  have hH'c : GeometricallyConnected (GeometricGroup H₀).val.X.hom :=
    MorphismProperty.pullback_snd _ _ hHc
  obtain ⟨g, hg⟩ := MaximalToriConjugate.maximalToriConjugate (GeometricGroup H₀) hH's
    (connected_of_geometricallyConnected hH'c) A' B' hA' hB'
  have hg' := conjugates_in_ambient H' hg
  rw [compose_restrict A H' a ha] at hg'
  let T := subgroupOfSubgroup H B
  let F := groupBaseChange k K
  have he : (subgroupOfSubgroup H' B').inclusion = (extendSubgroup K T).inclusion := by
    change F.map B.inclusion ≫ F.map H.inclusion = F.map (B.inclusion ≫ H.inclusion)
    rw [F.map_comp]
  have hsame : SameSubgroup (subgroupOfSubgroup H' B') (extendSubgroup K T) :=
    ⟨⟨𝟙 _, by rw [Category.id_comp, he]⟩, ⟨𝟙 _, by rw [Category.id_comp, he]⟩⟩
  have hfac := (subgroup_of_intersection (H := H) hH).mp ⟨𝟙 _, Category.id_comp _⟩
  exact ⟨T, hB, conjugates_maximal (conjugates_of_same hg' hsame) hA,
    subgroupTrans ⟨B.inclusion, rfl⟩ (hfac P (by simp)),
    subgroupTrans ⟨B.inclusion, rfl⟩ (hfac Q (by simp))⟩

private theorem maximalSplitTorusAbove (A : AffineAlgebraicGroup k) (I : ClosedSubgroup A.val)
    (hI : IsSplitTorus I.group) :
    ∃ S : ClosedSubgroup A.val, IsMaximalSplitTorus S ∧ IsSubgroupOf I S := by
  classical
  letI := A.property.1
  letI := A.property.2.1
  letI : IsLocallyNoetherian A.val.X.left := LocallyOfFiniteType.isLocallyNoetherian A.val.X.hom
  letI : IsNoetherianRing Γ(A.val.X.left, ⊤) :=
    IsLocallyNoetherian.component_noetherian ⟨⊤, isAffineOpen_top _⟩
  let ht (B : ClosedSubgroup A.val) := (definingIdeal B).height.toNat
  let p (n : ℕ) := ∃ B : ClosedSubgroup A.val, IsSplitTorus B.group ∧ IsSubgroupOf I B ∧ ht B = n
  have hp : ∃ n, p n := ⟨ht I, I, hI, ⟨𝟙 _, Category.id_comp _⟩, rfl⟩
  obtain ⟨S, hS, hIS, htS⟩ := Nat.find_spec hp
  refine ⟨S, ⟨hS, ?_⟩, hIS⟩
  intro B hB hSB
  obtain ⟨j, hj⟩ := hSB
  have hle := definingIdeal_le j hj
  have he : definingIdeal B = definingIdeal S := by
    by_contra hne
    letI := definingIdeal_prime_of_torus B (isTorus_of_split hB)
    letI := definingIdeal_prime_of_torus S (isTorus_of_split hS)
    have hlt := Ideal.height_strict_mono_of_isPrime_of_isPrime (lt_of_le_of_ne hle hne)
    have hB' := ENat.natCast_toNat (Ideal.height_ne_top_of_isPrime (I := definingIdeal B))
    have hS' := ENat.natCast_toNat (Ideal.height_ne_top_of_isPrime (I := definingIdeal S))
    have hmin : ht S ≤ ht B := htS.symm ▸ Nat.find_min' hp
      ⟨B, hB, subgroupTrans hIS ⟨j, hj⟩, rfl⟩
    exact (not_lt_of_ge hmin) (ENat.natCast_lt_natCast.mp (hB'.symm ▸ hS'.symm ▸ hlt))
  letI := factor_iso_of_definingIdeal_eq j hj he.symm
  exact ⟨inv j, by rw [← hj, IsIso.inv_hom_id_assoc]⟩

private theorem torusInLimitCentralizer {T : ClosedSubgroup G.val} (hT : IsTorus T.group)
    {c : Cocharacter G.val} (D : LimitDecomposition c)
    (hc : ∃ d : Cocharacter T.group, d ≫ T.inclusion = c) : IsSubgroupOf T D.centralizer := by
  obtain ⟨d, rfl⟩ := hc
  have h : Centralizes (d ≫ T.inclusion) T.inclusion.hom.hom := by
    apply (centralizes_iff _ _).mpr
    intro Y a b
    letI : IsCommMonObj T.group.X := torus_commutative (closedSubgroupAlgebraicGroup T) hT
    letI : CommMonoid (Y ⟶ T.group.X) := Hom.commMonoid
    exact (Commute.all a (b ≫ d.hom.hom)).map (IsMonHom.monoidHom T.inclusion.hom.hom Y)
  obtain ⟨x, hx⟩ := (D.centralizer_points _ _).mp h
  exact factor_group_through_subgroup D.centralizer T.inclusion x hx

/-- Two minimal rational parabolics have a common maximal split torus. -/
theorem commonMaximalSplitTorus : CommonMaximalSplitTorus.{u} := by
  intro k _ G hG P Q hP hQ
  obtain ⟨T, hT, hTg, ⟨j, hj⟩, hTQ⟩ := commonGeometricallyMaximalTorus hP.1 hQ.1
  let K := AlgebraicClosure k
  have hTm : IsMaximalTorus T := by
    refine ⟨hT, fun R hR hTR ↦ subgroup_descend K (hTg.2 (extendSubgroup K R) ?_ (subgroup_extend K hTR))⟩
    exact torus_after_algClosed_extension K (closedSubgroupAlgebraicGroup R) hR
  let Tₚ := restrictSubgroup T P j hj
  have hTp : IsMaximalTorus Tₚ := local_maximal_of_ambient P Tₚ (by
    rwa [compose_restrict T P j hj])
  obtain ⟨c, D, hPD, hLD, _⟩ := RationalCocharacter.rationalParabolicThroughTorus G P hP.1 Tₚ hTp
  let L := D.centralizer
  let c₀ := c ≫ (subgroupOfSubgroup P Tₚ).inclusion
  have hc₀ : c₀ = c ≫ T.inclusion := by
    change c ≫ (j ≫ P.inclusion) = c ≫ T.inclusion
    rw [hj]
  obtain ⟨i, hi⟩ := torusInLimitCentralizer hT D ⟨c, hc₀.symm⟩
  obtain ⟨e, _⟩ := subgroupOf_mutual_iso hPD.1 hPD.2
  let M := Specs.DiagonalizableGroups.IntegerCharacters.{u}
  let E : Multiplicative ℤ ≃* M := MulEquiv.ulift.symm
  letI : Group.FG M := Group.fg_of_surjective (f := E.toMonoidHom) E.surjective
  let U := Specs.DiagonalizableGroups.diagonalGroup k M
  have hU : IsSplitTorus U.val := ⟨1, multiplicative_group_iso⟩
  obtain ⟨I, p, hI, hcp⟩ := splitTorusImage U (closedSubgroupAlgebraicGroup L) hU (c ≫ i)
  obtain ⟨S, hS, b, hb⟩ := maximalSplitTorusAbove (closedSubgroupAlgebraicGroup L) I hI
  let S₀ := subgroupOfSubgroup L S
  have hf : (p ≫ b) ≫ S₀.inclusion = c₀ := by
    change (p ≫ b) ≫ (S.inclusion ≫ L.inclusion) = _
    rw [← Category.assoc (p ≫ b), Category.assoc p b, hb, hcp.1, Category.assoc, hi, hc₀]
  have hCT := LinearAlgebraicGroups.Reductive.TorusCentralizer.maximalTorusCentralizer G hG T hT
    ⟨(extendSubgroup K T).isClosedImmersion, hTg⟩
  have hST : IsSubgroupOf S₀ T := by
    have hC : Centralizes T.inclusion S₀.inclusion.hom.hom := by
      apply (centralizes_iff _ _).mpr
      intro Y a t
      have h := leviCentralizesSplitTorus P hP D e hLD S hS.1 (t ≫ i.hom.hom)
      have h' := ((centralizes_iff _ _).mp h Y (𝟙 Y) a).symm.map
        (IsMonHom.monoidHom L.inclusion.hom.hom Y)
      have hi' : i.hom.hom ≫ L.inclusion.hom.hom = T.inclusion.hom.hom :=
        (Grp.forget _).congr_map hi
      change Commute ((a ≫ S.inclusion.hom.hom) ≫ L.inclusion.hom.hom)
        ((𝟙 Y ≫ t ≫ i.hom.hom) ≫ L.inclusion.hom.hom) at h'
      change Commute (a ≫ S.inclusion.hom.hom ≫ L.inclusion.hom.hom) (t ≫ T.inclusion.hom.hom)
      simpa only [Category.id_comp, Category.assoc, hi'] using h'
    obtain ⟨a, ha⟩ := (hCT _ _).mp hC
    exact factor_group_through_subgroup T S₀.inclusion a ha
  have hmax : IsMaximalSplitTorus S₀ := by
    refine ⟨hS.1, ?_⟩
    intro R hR hSR
    obtain ⟨a, ha⟩ := hSR
    have hRₗ := torusInLimitCentralizer (isTorus_of_split hR) D
      ⟨(p ≫ b) ≫ a, by rw [Category.assoc, ha, hf]⟩
    obtain ⟨r, hr⟩ := hRₗ
    let Rₗ := restrictSubgroup R L r hr
    have heq : subgroupOfSubgroup L Rₗ = R := compose_restrict R L r hr
    have hSR : IsSubgroupOf S₀ R := ⟨a, ha⟩
    have h' : IsSubgroupOf S Rₗ := (subgroupOfSubgroup_le L S Rₗ).mp (heq.symm ▸ hSR)
    exact heq ▸ (subgroupOfSubgroup_le L Rₗ S).mpr (hS.2 Rₗ hR h')
  exact ⟨S₀, hmax, subgroupTrans hST ⟨j, hj⟩, subgroupTrans hST hTQ⟩

end

end LinearAlgebraicGroups.Relative.RelativeWeylScheme
