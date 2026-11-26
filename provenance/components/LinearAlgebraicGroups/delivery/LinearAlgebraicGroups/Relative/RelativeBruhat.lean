import Specs.LinearAlgebraicGroups.Relative.RelativeBruhat
import LinearAlgebraicGroups.Relative.MaximalSplitTori
import LinearAlgebraicGroups.Flag.ProjectiveFlags
import LinearAlgebraicGroups.Flag.SmoothOrbit
import Batteries.Tactic.OpenPrivate

import LinearAlgebraicGroups.Relative.RelativeWeylScheme
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj Pointwise

namespace LinearAlgebraicGroups.Relative.RelativeBruhat

open LinearAlgebraicGroups.Specs
open Specs.Relative.RelativeBruhat
open Specs.Relative.RelativeWeylScheme
open Specs.Relative.MaximalSplitTori (IsMinimalParabolic IsMaximalSplitTorus)
open Specs.CharacterDescent (Cocharacter)
open Specs.GeometricRadicals (IsReductive)
open Specs.GeometricBorelConjugacy (ConjugatesSubgroups subgroupOfSubgroup)
open Specs.BorelsAndChambers (contractingSubgroup)
open Specs.RankOneFlag (SameSubgroup)
open Specs.SchemeDerivedGroup (IsSubgroupOf)
open Specs.QuotientEmbedding (Presentation)
open Specs.SimpleParabolicProduct (doubleCoset)
open Specs.Unipotent (closedSubgroupAlgebraicGroup)
open LinearAlgebraicGroups.CocharacterDynamics

open private innerIso transportSubgroup quotientSeparatedFiniteType subgroupQuotientAction
  quotientAct quotientAct_comp quotientAct_projection
  from LinearAlgebraicGroups.Reductive.BorelProper
open private minimalParabolicTransport maximalSplitInParabolic maximalSplitOfConjugate
  conjugates_of_sameTransport
  from LinearAlgebraicGroups.Relative.MaximalSplitTori
open private restrictSubgroup compose_restrict conjugates_in_ambient conjugates_trans
  from LinearAlgebraicGroups.Reductive.MaximalToriConjugate
open private conjugates_inverse from LinearAlgebraicGroups.RootData.BorelNormalizer
open private radical_transport from LinearAlgebraicGroups.RootData.OrderedRootProducts
open private subgroupIso_of_same from LinearAlgebraicGroups.RootData.RankOneFlag
open private pushSubgroup from LinearAlgebraicGroups.RootData.OrderedRootProducts
open private quotient_rightMul geometricPoint_of_commonImage
  section_mem_of_le monoSubgroup orbitProjection_eq
  cocharacterPoint_comp
  from LinearAlgebraicGroups.Flag.BruhatOrbitParametrization
open private projection_eq_iff from LinearAlgebraicGroups.Flag.QuotientEmbedding
open private centralizes_iff conjugateLe_iff from LinearAlgebraicGroups.Affine.Stabilizers
open private polynomial_to_laurent_dense from LinearAlgebraicGroups.Flag.StandardParabolicLevi

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 900000
set_option linter.style.haveILetI false

universe u

variable {k : Type u} [Field k] {G : AffineAlgebraicGroup k}

private theorem section_conjugated {M : GroupScheme k} {A B : ClosedSubgroup M}
    {t : 𝟙_ (SchemeOver k) ⟶ M.X} (h : ConjugatesSubgroups t A B)
    {Y : SchemeOver k} {g : Y ⟶ M.X} (hg : g ∈ SubgroupSections A Y) :
    (toUnit Y ≫ t) * g * (toUnit Y ≫ t)⁻¹ ∈ SubgroupSections B Y := by
  obtain ⟨e, he⟩ := h
  change (∃ a : Y ⟶ A.group.X, a ≫ A.inclusion.hom.hom = g) at hg
  obtain ⟨a, rfl⟩ := hg
  refine ⟨a ≫ e.hom.hom.hom, ?_⟩
  change a ≫ e.hom.hom.hom ≫ B.inclusion.hom.hom = _
  change e.hom.hom.hom ≫ B.inclusion.hom.hom =
    (toUnit A.group.X ≫ t) * A.inclusion.hom.hom * (toUnit A.group.X ≫ t)⁻¹ at he
  rw [he]
  simp only [MonObj.comp_mul, GrpObj.comp_inv, comp_toUnit_assoc]

private theorem normalizes_of_conjugates {M : GroupScheme k} {S : ClosedSubgroup M}
    {n : 𝟙_ (SchemeOver k) ⟶ M.X} (h : ConjugatesSubgroups n S S) :
    Normalizes S.inclusion n := by
  apply (LinearAlgebraicGroups.normalizesIff k S.inclusion S.isClosedImmersion _ _).2
  constructor
  · apply (conjugateLe_iff _ _).2
    intro Y t s
    rw [show t = toUnit Y from Subsingleton.elim _ _]
    exact section_conjugated h ⟨s, rfl⟩
  · apply (conjugateLe_iff _ _).2
    intro Y t s
    rw [show t = toUnit Y from Subsingleton.elim _ _]
    exact section_conjugated (conjugates_inverse h) ⟨s, rfl⟩

private theorem conjugates_transport (A : ClosedSubgroup G.val)
    (g : 𝟙_ (SchemeOver k) ⟶ G.val.X) :
    ConjugatesSubgroups g A (transportSubgroup A (innerIso g)) := by
  refine conjugates_of_sameTransport g ⟨?_, ?_⟩ <;>
    exact ⟨𝟙 _, Category.id_comp _⟩

private theorem conjugate_in_parabolic {P A B : ClosedSubgroup G.val}
    (hP : IsMinimalParabolic G P) (hA : IsMaximalSplitTorus A)
    (hB : IsMaximalSplitTorus B) (hAP : IsSubgroupOf A P) (hBP : IsSubgroupOf B P) :
    ∃ a ∈ SubgroupSections P (𝟙_ (SchemeOver k)), ConjugatesSubgroups a A B := by
  obtain ⟨j, hj⟩ := hAP
  obtain ⟨i, hi⟩ := hBP
  let A' := restrictSubgroup A P j hj
  let B' := restrictSubgroup B P i hi
  have ha : subgroupOfSubgroup P A' = A := compose_restrict A P j hj
  have hb : subgroupOfSubgroup P B' = B := compose_restrict B P i hi
  have ha' := maximalSplitInParabolic (P := P) (S := A') (ha.symm ▸ hA)
  have hb' := maximalSplitInParabolic (P := P) (S := B') (hb.symm ▸ hB)
  obtain ⟨_, L, hL, hRad, _, _, _⟩ := MaximalSplitTori.minimalParabolicLevi G P hP A' ha'
  obtain ⟨e, _⟩ := subgroupIso_of_same hL
  let U := pushSubgroup e.symm (contractingSubgroup L)
  have hU := radical_transport (A := closedSubgroupAlgebraicGroup L.parabolic)
    (B := closedSubgroupAlgebraicGroup P) e.symm (contractingSubgroup L) hRad.1
  obtain ⟨u, hu⟩ := MaximalSplitTori.maximalSplitToriConjugateByRadical G P hP U hU A' B' ha' hb'
  refine ⟨(u ≫ U.inclusion.hom.hom) ≫ P.inclusion.hom.hom, ⟨_, rfl⟩, ?_⟩
  simpa only [ha, hb] using conjugates_in_ambient P hu

private theorem rational_normalizer_factorization (common : CommonMaximalSplitTorus.{u})
    (hG : IsReductive G) {P S : ClosedSubgroup G.val} (hS : IsMaximalSplitTorus S)
    (hP : IsMinimalParabolic G P) (hSP : IsSubgroupOf S P) (D : QuotientData S)
    (g : 𝟙_ (SchemeOver k) ⟶ G.val.X) :
    ∃ (n : 𝟙_ (SchemeOver k) ⟶ D.normalizer.group.X)
      (a b : 𝟙_ (SchemeOver k) ⟶ P.group.X),
      g = (a ≫ P.inclusion.hom.hom) * (n ≫ D.normalizer.inclusion.hom.hom) *
        (b ≫ P.inclusion.hom.hom) := by
  let Q := transportSubgroup P (innerIso g)
  let S' := transportSubgroup S (innerIso g)
  have hQ := minimalParabolicTransport hP (innerIso g)
  have hgP : ConjugatesSubgroups g P Q := conjugates_transport P g
  have hgS : ConjugatesSubgroups g S S' := conjugates_transport S g
  have hS' := maximalSplitOfConjugate hgS hS
  have hS'Q : IsSubgroupOf S' Q := by
    obtain ⟨j, hj⟩ := hSP
    refine ⟨j, ?_⟩
    change j ≫ P.inclusion ≫ (innerIso g).hom = S.inclusion ≫ (innerIso g).hom
    rw [← Category.assoc, hj]
  obtain ⟨T, hT, hTP, hTQ⟩ := common G hG P Q hP hQ
  obtain ⟨a, ha, hTa⟩ := conjugate_in_parabolic hP hT hS hTP hSP
  obtain ⟨b, hb, hTb⟩ := conjugate_in_parabolic hQ hS' hT hS'Q hTQ
  have hN : ConjugatesSubgroups (a * (b * g)) S S :=
    conjugates_trans (conjugates_trans hgS hTb) hTa
  obtain ⟨n, hn⟩ := (D.normalizerProperty _ _).mp (normalizes_of_conjugates hN)
  change (∃ a' : 𝟙_ (SchemeOver k) ⟶ P.group.X, a' ≫ P.inclusion.hom.hom = a) at ha
  obtain ⟨a', ha'⟩ := ha
  have hb' : g⁻¹ * b * g ∈ SubgroupSections P (𝟙_ (SchemeOver k)) := by
    simpa only [toUnit_unit, Category.id_comp, inv_inv] using
      section_conjugated (conjugates_inverse hgP) hb
  change (∃ b' : 𝟙_ (SchemeOver k) ⟶ P.group.X,
    b' ≫ P.inclusion.hom.hom = g⁻¹ * b * g) at hb'
  obtain ⟨b', hb'⟩ := hb'
  refine ⟨n, a'⁻¹, b'⁻¹, ?_⟩
  rw [GrpObj.inv_comp, GrpObj.inv_comp, ha', hb', hn]
  group

private theorem rational_coverage
    (common : CommonMaximalSplitTorus.{u}) (hG : IsReductive G)
    {S P : ClosedSubgroup G.val} (hS : IsMaximalSplitTorus S)
    (hP : IsMinimalParabolic G P) (hSP : IsSubgroupOf S P) (D : QuotientData S)
    (hInt : UnipotentRadicalIntersection.IsSchemeIntersection {D.normalizer, P} D.centralizer)
    [hZ : (MonoidHom.range (IsMonHom.monoidHom D.inclusion.hom.hom
      (𝟙_ (SchemeOver k)))).Normal]
    (e : (𝟙_ (SchemeOver k) ⟶ D.normalizer.group.X) ⧸
      (MonoidHom.range (IsMonHom.monoidHom D.inclusion.hom.hom
        (𝟙_ (SchemeOver k)))) ≃* D.splitImage.labels)
    (he : ∀ m, rationalProjection D m = D.splitImage.constantGroup.sectionPoint
      (e (QuotientGroup.mk m)))
    (n : D.splitImage.labels → (𝟙_ (SchemeOver k) ⟶ D.normalizer.group.X))
    (hn : ∀ w, rationalProjection D (n w) = D.splitImage.constantGroup.sectionPoint w) :
    (⋃ w, doubleCoset P (𝟙_ (SchemeOver k)) (n w ≫ D.normalizer.inclusion.hom.hom)) =
      Set.univ := by
  classical
  apply Set.eq_univ_of_forall
  intro g
  obtain ⟨m, a, b, hg⟩ := rational_normalizer_factorization common hG hS hP hSP D g
  let w := e (QuotientGroup.mk m)
  have heq := (hn w).trans (he m).symm
  have hz : ((n w)⁻¹ * m) ≫ D.projection.hom.hom = (1 : 𝟙_ (SchemeOver k) ⟶ D.group.val.X) := by
    rw [MonObj.mul_comp, GrpObj.inv_comp]
    change (rationalProjection D (n w))⁻¹ * rationalProjection D m = 1
    exact inv_mul_eq_one.mpr heq
  let d := (n w)⁻¹ * m
  have hd : d ≫ D.normalizer.inclusion.hom.hom ∈ SubgroupSections D.centralizer _ := by
    have pb := D.quotientProperty.1
    have hd' : d ≫ D.projection.hom.hom = toUnit _ ≫ η[D.group.val.X] := hz
    let z := pb.lift d (toUnit _) hd'
    refine ⟨z, ?_⟩
    change z ≫ D.centralizer.inclusion.hom.hom = d ≫ D.normalizer.inclusion.hom.hom
    have hzi := pb.lift_fst d (toUnit _) hd'
    change z ≫ D.inclusion.hom.hom = d at hzi
    have hinc := (Grp.forget (SchemeOver k)).congr_map D.inclusionProperty
    change D.inclusion.hom.hom ≫ D.normalizer.inclusion.hom.hom =
      D.centralizer.inclusion.hom.hom at hinc
    rw [← hinc, ← Category.assoc, hzi]
  have hp := (hInt _ _).mp hd P (by simp)
  apply Set.mem_iUnion.mpr
  refine ⟨w, ?_⟩
  unfold doubleCoset
  rw [toUnit_unit, Category.id_comp]
  have hg' : g = (a ≫ P.inclusion.hom.hom) * (n w ≫ D.normalizer.inclusion.hom.hom) *
      ((d ≫ D.normalizer.inclusion.hom.hom) * (b ≫ P.inclusion.hom.hom)) := by
    rw [hg]
    simp only [d, MonObj.mul_comp, GrpObj.inv_comp]
    group
  rw [hg']
  exact Set.mul_mem_mul
    (Set.mul_mem_mul (show a ≫ P.inclusion.hom.hom ∈ SubgroupSections P _ from ⟨a, rfl⟩)
      (Set.mem_singleton _))
    ((SubgroupSections P _).mul_mem hp ⟨b, rfl⟩)

private theorem comp_doubleOrbitMap (P : ClosedSubgroup G.val)
    (n : 𝟙_ (SchemeOver k) ⟶ G.val.X) {Y : SchemeOver k}
    (f : Y ⟶ P.group.X ⊗ P.group.X) :
    f ≫ doubleOrbitMap P n =
      (f ≫ fst _ _ ≫ P.inclusion.hom.hom) * (toUnit Y ≫ n) *
        (f ≫ snd _ _ ≫ P.inclusion.hom.hom) := by
  simp only [doubleOrbitMap, MonObj.comp_mul, comp_toUnit_assoc]

private theorem orbit_map_formula {P : ClosedSubgroup G.val} (Q : Presentation P)
    (n : 𝟙_ (SchemeOver k) ⟶ G.val.X)
    (O : SmoothOrbit.Presentation (subgroupQuotientAction (B := P) Q) (n ≫ Q.projection))
    {Y : SchemeOver k} (a : Y ⟶ P.group.X) :
    a ≫ O.projection ≫ O.openInClosure ≫ SmoothOrbit.closureInclusion _ _ =
      ((a ≫ P.inclusion.hom.hom) * (toUnit Y ≫ n)) ≫ Q.projection := by
  rw [orbitProjection_eq O, SmoothOrbit.orbitMap]
  change a ≫ lift (𝟙 P.group.X) (toUnit P.group.X ≫ n ≫ Q.projection) ≫
    quotientAct Q (fst _ _ ≫ P.inclusion.hom.hom) (snd _ _) = _
  simp only [← Category.assoc a, quotientAct_comp, Category.comp_id,
    lift_fst_assoc, lift_snd, comp_toUnit]
  rw [← Category.assoc (toUnit Y), quotientAct_projection]

private theorem multiplication_pullback {P : ClosedSubgroup G.val} (Q : Presentation P)
    (n : 𝟙_ (SchemeOver k) ⟶ G.val.X) {X O : SchemeOver k} {i : O ⟶ Q.scheme}
    {j : X ⟶ G.val.X} {r : X ⟶ O} (pb : IsPullback j r Q.projection i)
    (q : P.group.X ⟶ O)
    (hq : ∀ {Y : SchemeOver k} (a : Y ⟶ P.group.X),
      a ≫ q ≫ i = ((a ≫ P.inclusion.hom.hom) * (toUnit Y ≫ n)) ≫ Q.projection)
    (p : P.group.X ⊗ P.group.X ⟶ X)
    (hp : p ≫ j = doubleOrbitMap P n) (hr : p ≫ r = fst _ _ ≫ q) :
    IsPullback p (fst _ _) r q := by
  have lifts (s : PullbackCone r q) : ∃ b : s.pt ⟶ P.group.X,
      lift s.snd b ≫ p = s.fst := by
    let a := s.snd
    let g := (a ≫ P.inclusion.hom.hom) * (toUnit s.pt ≫ n)
    have h : g ≫ Q.projection = (s.fst ≫ j) ≫ Q.projection := by
      rw [← hq a, ← Category.assoc a, ← s.condition]
      simp only [Category.assoc, pb.w]
    obtain ⟨b, hb⟩ := (projection_eq_iff Q _ _).mp h
    change b ≫ P.inclusion.hom.hom = g⁻¹ * (s.fst ≫ j) at hb
    refine ⟨b, pb.hom_ext ?_ ?_⟩
    · rw [Category.assoc, hp, comp_doubleOrbitMap]
      simp only [lift_fst_assoc, lift_snd_assoc, hb]
      change g * (g⁻¹ * _) = _
      exact mul_inv_cancel_left _ _
    · rw [Category.assoc, hr, lift_fst_assoc, s.condition]
  choose b hb using lifts
  refine IsPullback.of_isLimit (PullbackCone.IsLimit.mk hr
    (fun s ↦ lift s.snd (b s)) hb (fun s ↦ lift_fst _ _) ?_)
  intro s f hf ha
  apply CartesianMonoidalCategory.hom_ext
  · rwa [lift_fst]
  · rw [lift_snd]
    letI := monoSubgroup P
    apply (cancel_mono P.inclusion.hom.hom).mp
    have h : f ≫ doubleOrbitMap P n = lift s.snd (b s) ≫ doubleOrbitMap P n := by
      rw [← hp, ← Category.assoc, ← Category.assoc, hf, hb]
    simp only [comp_doubleOrbitMap, ← Category.assoc _ (fst _ _) P.inclusion.hom.hom,
      ← Category.assoc _ (snd _ _) P.inclusion.hom.hom, ha, lift_fst, lift_snd] at h
    exact mul_left_cancel h

private noncomputable def doubleOrbitOfFlag {P : ClosedSubgroup G.val}
    (Q : Presentation P) (n : 𝟙_ (SchemeOver k) ⟶ G.val.X)
    (O : SmoothOrbit.Presentation (subgroupQuotientAction (B := P) Q) (n ≫ Q.projection)) :
    DoubleOrbit P n := by
  let i := O.openInClosure ≫ SmoothOrbit.closureInclusion _ _
  let j := pullback.fst Q.projection i
  let r := pullback.snd Q.projection i
  let m := doubleOrbitMap P n
  let q := fst P.group.X P.group.X ≫ O.projection
  have pb := IsPullback.of_hasPullback Q.projection i
  have hcomm : m ≫ Q.projection = q ≫ i := by
    change m ≫ Q.projection = (fst _ _ ≫ O.projection) ≫ i
    rw [Category.assoc, orbit_map_formula Q n O]
    exact quotient_rightMul Q _ (snd _ _)
  let p := pb.lift m q hcomm
  have hp : p ≫ j = m := pb.lift_fst m q hcomm
  have hr : p ≫ r = q := pb.lift_snd m q hcomm
  have hp' : IsPullback p (fst _ _) r O.projection :=
    multiplication_pullback Q n pb O.projection (orbit_map_formula Q n O) p hp hr
  letI : IsOpenImmersion O.openInClosure.left := O.isOpen
  have hi : IsImmersion i.left := by
    change IsImmersion (O.openInClosure.left ≫ (SmoothOrbit.orbitMap _ _).left.imageι)
    infer_instance
  refine ⟨pullback Q.projection i, j,
    MorphismProperty.of_isPullback (P := @IsImmersion) ((pb.map (Over.forget _)).flip) hi,
    p, hp, ?_, ?_, ?_⟩
  · exact MorphismProperty.of_isPullback (P := @Flat) ((hp'.map (Over.forget _)).flip) O.flat
  · exact MorphismProperty.of_isPullback (P := @Surjective) ((hp'.map (Over.forget _)).flip) O.surjective
  · exact MorphismProperty.of_isPullback (P := @LocallyOfFinitePresentation)
      ((hp'.map (Over.forget _)).flip) O.finitePresentation

private theorem exists_doubleOrbit {P : ClosedSubgroup G.val} (hP : IsMinimalParabolic G P)
    (Q : Presentation P) (hQ : IsProper Q.scheme.hom)
    (n : 𝟙_ (SchemeOver k) ⟶ G.val.X) : Nonempty (DoubleOrbit P n) := by
  letI := hQ
  obtain ⟨O⟩ := SmoothOrbit.schemeOrbit k (closedSubgroupAlgebraicGroup P) Q.scheme
    (subgroupQuotientAction (B := P) Q) (n ≫ Q.projection) hP.1.2.1
    inferInstance inferInstance inferInstance
  exact ⟨doubleOrbitOfFlag Q n O⟩

private theorem conjugates_normalizer_sections {S : ClosedSubgroup G.val}
    {n : 𝟙_ (SchemeOver k) ⟶ G.val.X} (hn : Normalizes S.inclusion n) :
    (∀ (Y : SchemeOver k) (s : Y ⟶ S.group.X),
      ∃ t : Y ⟶ S.group.X, t ≫ S.inclusion.hom.hom =
        (toUnit Y ≫ n) * (s ≫ S.inclusion.hom.hom) * (toUnit Y ≫ n)⁻¹) ∧
    (∀ (Y : SchemeOver k) (s : Y ⟶ S.group.X),
      ∃ t : Y ⟶ S.group.X, t ≫ S.inclusion.hom.hom =
        (toUnit Y ≫ n)⁻¹ * (s ≫ S.inclusion.hom.hom) * (toUnit Y ≫ n)) := by
  obtain ⟨h, hi⟩ := (LinearAlgebraicGroups.normalizesIff k S.inclusion
    S.isClosedImmersion _ n).1 hn
  constructor
  · intro Y s
    exact (conjugateLe_iff _ _).1 h Y (toUnit Y) s
  · intro Y s
    simpa only [GrpObj.comp_inv, inv_inv] using
      (conjugateLe_iff _ _).1 hi Y (toUnit Y) s

private theorem normalizer_torus_mem {S P : ClosedSubgroup G.val} (hSP : IsSubgroupOf S P)
    {n : 𝟙_ (SchemeOver k) ⟶ G.val.X} (hn : Normalizes S.inclusion n)
    {Y : SchemeOver k} (s : Y ⟶ S.group.X) :
    (toUnit Y ≫ n)⁻¹ * (s ≫ S.inclusion.hom.hom) * (toUnit Y ≫ n) ∈
      SubgroupSections P Y :=
  section_mem_of_le hSP ((conjugates_normalizer_sections hn).2 Y s)

private theorem normalizer_preserves_centralizer {S : ClosedSubgroup G.val}
    {n : 𝟙_ (SchemeOver k) ⟶ G.val.X} (hn : Normalizes S.inclusion n)
    {Y : SchemeOver k} {z : Y ⟶ G.val.X} (hz : Centralizes S.inclusion z) :
    Centralizes S.inclusion ((toUnit Y ≫ n)⁻¹ * z * (toUnit Y ≫ n)) := by
  apply (centralizes_iff _ _).2
  intro X f s
  let r := toUnit X ≫ n
  let t := s ≫ S.inclusion.hom.hom
  obtain ⟨a, ha⟩ := (conjugates_normalizer_sections hn).1 X s
  have hc := ((centralizes_iff _ _).1 hz X f a).eq
  change (f ≫ z) * (a ≫ S.inclusion.hom.hom) = (a ≫ S.inclusion.hom.hom) * (f ≫ z) at hc
  rw [ha] at hc
  simp only [MonObj.comp_mul, GrpObj.comp_inv, comp_toUnit_assoc]
  change r⁻¹ * (f ≫ z) * r * t = t * (r⁻¹ * (f ≫ z) * r)
  calc
    _ = r⁻¹ * ((f ≫ z) * (r * t * r⁻¹)) * r := by group
    _ = r⁻¹ * ((r * t * r⁻¹) * (f ≫ z)) * r := by rw [hc]
    _ = _ := by group

/-- Apply the Levi retraction to the left parabolic factor. The cocharacter
fixes the normalizer cosets, so specialization leaves their equality intact. -/
private theorem normalizer_cosets_of_translate {S P : ClosedSubgroup G.val}
    (D : QuotientData S)
    (hInt : UnipotentRadicalIntersection.IsSchemeIntersection {D.normalizer, P} D.centralizer)
    (hSP : IsSubgroupOf S P) (Q : Presentation P)
    (c : Cocharacter S.group) {d : Cocharacter G.val} (L : LimitDecomposition d)
    (hc : d = c ≫ S.inclusion)
    (hPL : SameSubgroup P L.parabolic)
    (hL : RepresentsSubgroup L.centralizer (fun _ g ↦ Centralizes S.inclusion g))
    {n n' : 𝟙_ (SchemeOver k) ⟶ G.val.X}
    (hn : Normalizes S.inclusion n) (hn' : Normalizes S.inclusion n')
    (K : Type u) [Field K] [Algebra k K]
    (p : Over.mk (fieldSpecMap k K) ⟶ G.val.X)
    (hp : p ∈ SubgroupSections P (Over.mk (fieldSpecMap k K)))
    (he : (p * (toUnit (Over.mk (fieldSpecMap k K)) ≫ n)) ≫ Q.projection =
      (toUnit (Over.mk (fieldSpecMap k K)) ≫ n') ≫ Q.projection) :
    (toUnit (Over.mk (fieldSpecMap k K)) ≫ n) ≫ Q.projection =
      (toUnit (Over.mk (fieldSpecMap k K)) ≫ n') ≫ Q.projection := by
  let R : TestAlgebra k := CommAlgCat.of k K
  let Y := (testSpec k).obj (.op R)
  let p₀ : Y ⟶ G.val.X := p
  change p₀ ∈ SubgroupSections P Y at hp
  change (p₀ * (toUnit Y ≫ n)) ≫ Q.projection = (toUnit Y ≫ n') ≫ Q.projection at he
  let X := (testSpec k).obj (.op (polynomialAlgebra R))
  let V := (testSpec k).obj (.op (laurentAlgebra R))
  let l : V ⟶ X := (testSpec k).map (polynomialToLaurent R).op
  let v : V ⟶ Y := (testSpec k).map (laurentConstants R).op
  let e₀ : Y ⟶ X := (testSpec k).map (polynomialEvaluate R 0).op
  have hpL := section_mem_of_le hPL.1 hp
  change ∃ a : Y ⟶ L.parabolic.group.X, a ≫ L.parabolic.inclusion.hom.hom = p₀ at hpL
  obtain ⟨a, ha⟩ := hpL
  let z : Y ⟶ G.val.X := a ≫ (L.limit ≫ L.centralizer.inclusion).hom.hom
  have hz : Centralizes S.inclusion z :=
    (hL _ _).2 ⟨a ≫ L.limit.hom.hom, Category.assoc _ _ _⟩
  have hz' := normalizer_preserves_centralizer hn hz
  have hzP : (toUnit Y ≫ n)⁻¹ * z * (toUnit Y ≫ n) ∈ SubgroupSections P Y :=
    (hInt _ _).1 ((D.centralizerProperty _ _).1 hz') P (by simp)
  obtain ⟨f, hf, hf₀⟩ := L.limit_points R a
  let s₀ : V ⟶ S.group.X := cocharacterPoint c (laurentAlgebra R) (laurentParameter R)
  let s : V ⟶ G.val.X := s₀ ≫ S.inclusion.hom.hom
  let r : V ⟶ G.val.X := toUnit V ≫ n
  let r' : V ⟶ G.val.X := toUnit V ≫ n'
  have hLaurent : l ≫ f = s * (v ≫ p₀) * s⁻¹ := by
    change l ≫ f = orbit d (a ≫ L.parabolic.inclusion.hom.hom) at hf
    rw [hf, ha, hc, orbit, cocharacterPoint_comp]
  have heV : ((v ≫ p₀) * r) ≫ Q.projection = r' ≫ Q.projection := by
    have h := congrArg (v ≫ ·) he
    change v ≫ ((p₀ * (toUnit Y ≫ n)) ≫ Q.projection) =
      v ≫ ((toUnit Y ≫ n') ≫ Q.projection) at h
    rw [← Category.assoc v, MonObj.comp_mul, comp_toUnit_assoc, ← Category.assoc v,
      comp_toUnit_assoc] at h
    exact h
  have hs : r⁻¹ * s * r ∈ SubgroupSections P V := normalizer_torus_mem hSP hn s₀
  have hs' : r'⁻¹ * s * r' ∈ SubgroupSections P V := normalizer_torus_mem hSP hn' s₀
  have hOrbit : (s * (v ≫ p₀) * s⁻¹ * r) ≫ Q.projection = r' ≫ Q.projection := by
    calc
      _ = (s * ((v ≫ p₀) * r)) ≫ Q.projection := by
        apply (projection_eq_iff Q _ _).2
        convert hs using 1
        group
      _ = (s * r') ≫ Q.projection := by
        rw [← quotientAct_projection Q, heV, quotientAct_projection]
      _ = _ := by
        symm
        exact (projection_eq_iff Q _ _).2 (by simpa only [mul_assoc] using hs')
  let F : X ⟶ Q.scheme := ((show X ⟶ G.val.X from f) * (toUnit X ≫ n)) ≫ Q.projection
  let F' : X ⟶ Q.scheme := (toUnit X ≫ n') ≫ Q.projection
  have hagree : l ≫ F = l ≫ F' := by
    simp only [F, F', ← Category.assoc l, MonObj.comp_mul, comp_toUnit, hLaurent]
    exact hOrbit
  haveI : IsReduced X.left := by
    change IsReduced (Spec (CommRingCat.of (Polynomial K)))
    infer_instance
  haveI : IsSeparated Q.scheme.hom := (quotientSeparatedFiniteType Q).1
  haveI : IsDominant l.left := ⟨polynomial_to_laurent_dense R⟩
  have hEq : F = F' := by
    apply Over.OverMorphism.ext
    exact ext_of_isDominant_of_isSeparated Q.scheme.hom
      ((Over.w F).trans (Over.w F').symm) l.left (congrArg (fun x ↦ x.left) hagree)
  have hzero : e₀ ≫ f = z := hf₀
  have hh := congrArg (e₀ ≫ ·) hEq
  simp only [F, F', ← Category.assoc e₀, MonObj.comp_mul, comp_toUnit, hzero]
    at hh
  have hfix : ((toUnit Y ≫ n) ≫ Q.projection) =
      (z * (toUnit Y ≫ n)) ≫ Q.projection := by
    apply (projection_eq_iff Q _ _).2
    simpa only [mul_assoc] using hzP
  exact hfix.trans hh

private theorem labels_eq_of_equal_cosets {S P : ClosedSubgroup G.val}
    (D : QuotientData S)
    (hInt : UnipotentRadicalIntersection.IsSchemeIntersection {D.normalizer, P} D.centralizer)
    (Q : Presentation P) {Y : SchemeOver k} (y : Y.left)
    {m n : 𝟙_ (SchemeOver k) ⟶ D.normalizer.group.X} {w v : D.splitImage.labels}
    (hm : rationalProjection D m = D.splitImage.constantGroup.sectionPoint w)
    (hn : rationalProjection D n = D.splitImage.constantGroup.sectionPoint v)
    (he : ((toUnit Y ≫ m) ≫ D.normalizer.inclusion.hom.hom) ≫ Q.projection =
      ((toUnit Y ≫ n) ≫ D.normalizer.inclusion.hom.hom) ≫ Q.projection) : w = v := by
  let a := toUnit Y ≫ m
  let b := toUnit Y ≫ n
  let d := a⁻¹ * b
  have hP : d ≫ D.normalizer.inclusion.hom.hom ∈ SubgroupSections P Y := by
    simpa only [d, MonObj.mul_comp, GrpObj.inv_comp] using
      (projection_eq_iff Q _ _).1 he
  have hC := (hInt Y _).2 (by
    intro H hH
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hH
    rcases hH with rfl | rfl
    · exact ⟨d, rfl⟩
    · exact hP)
  obtain ⟨z, hz⟩ := hC
  change z ≫ D.centralizer.inclusion.hom.hom = d ≫ D.normalizer.inclusion.hom.hom at hz
  letI := monoSubgroup D.normalizer
  have hinc := (Grp.forget (SchemeOver k)).congr_map D.inclusionProperty
  change D.inclusion.hom.hom ≫ D.normalizer.inclusion.hom.hom =
    D.centralizer.inclusion.hom.hom at hinc
  have hd : d = z ≫ D.inclusion.hom.hom := (cancel_mono D.normalizer.inclusion.hom.hom).1
    (by rw [Category.assoc, hinc, hz])
  have hker := D.quotientProperty.1.w
  change D.inclusion.hom.hom ≫ D.projection.hom.hom = toUnit _ ≫ η[D.group.val.X] at hker
  have hproj : d ≫ D.projection.hom.hom = 1 := by
    rw [hd, Category.assoc, hker, comp_toUnit_assoc]
    rfl
  have hproj' : a ≫ D.projection.hom.hom = b ≫ D.projection.hom.hom := by
    apply inv_mul_eq_one.mp
    simpa only [d, MonObj.mul_comp, GrpObj.inv_comp] using hproj
  change m ≫ D.projection.hom.hom = _ at hm
  change n ≫ D.projection.hom.hom = _ at hn
  simp only [a, b, Category.assoc, hm, hn] at hproj'
  have h := congrArg (D.splitImage.constantGroup.families Y) hproj'
  rw [D.splitImage.constantGroup.constant, D.splitImage.constantGroup.constant] at h
  exact congrArg (fun f : LocallyConstant Y.left D.splitImage.labels ↦ f y) h

private theorem range_doubleOrbit (P : ClosedSubgroup G.val)
    (n : 𝟙_ (SchemeOver k) ⟶ G.val.X) (O : DoubleOrbit P n) :
    Set.range O.inclusion.left = Set.range (doubleOrbitMap P n).left := by
  letI : Surjective O.projection.left := O.surjective
  rw [← O.factors]
  change Set.range O.inclusion.left = Set.range (O.inclusion.left ∘ O.projection.left)
  rw [Set.range_comp, Set.range_eq_univ.mpr O.projection.left.surjective, Set.image_univ]

private theorem pairwise_orbits {S P : ClosedSubgroup G.val} (D : QuotientData S)
    (hInt : UnipotentRadicalIntersection.IsSchemeIntersection {D.normalizer, P} D.centralizer)
    (Q : Presentation P) (hSP : IsSubgroupOf S P)
    (c : Cocharacter S.group) {d : Cocharacter G.val} (L : LimitDecomposition d)
    (hc : d = c ≫ S.inclusion)
    (hPL : SameSubgroup P L.parabolic)
    (hL : RepresentsSubgroup L.centralizer (fun _ g ↦ Centralizes S.inclusion g))
    (n : D.splitImage.labels → (𝟙_ (SchemeOver k) ⟶ D.normalizer.group.X))
    (hn : ∀ w, rationalProjection D (n w) = D.splitImage.constantGroup.sectionPoint w)
    (O : ∀ w, DoubleOrbit P (n w ≫ D.normalizer.inclusion.hom.hom)) :
    Pairwise (fun w v ↦ Disjoint (Set.range (O w).inclusion.left)
      (Set.range (O v).inclusion.left)) := by
  intro w v hne
  rw [range_doubleOrbit, range_doubleOrbit]
  apply Set.disjoint_left.mpr
  rintro _ ⟨x, rfl⟩ ⟨y, hy⟩
  let g := fun w ↦ n w ≫ D.normalizer.inclusion.hom.hom
  obtain ⟨K, _, _, _, a, b, hab⟩ := geometricPoint_of_commonImage
    (doubleOrbitMap P (g w)) (doubleOrbitMap P (g v)) x y hy.symm
  let Y := Over.mk (fieldSpecMap k K)
  let p : Y ⟶ P.group.X := (b ≫ fst _ _)⁻¹ * (a ≫ fst _ _)
  have hp : p ≫ P.inclusion.hom.hom ∈ SubgroupSections P Y := ⟨p, rfl⟩
  have h := congrArg (· ≫ Q.projection) hab
  rw [comp_doubleOrbitMap, comp_doubleOrbitMap] at h
  let a₀ := (a ≫ fst _ _ ≫ P.inclusion.hom.hom) * (toUnit Y ≫ g w)
  let b₀ := (b ≫ fst _ _ ≫ P.inclusion.hom.hom) * (toUnit Y ≫ g v)
  change (a₀ * ((a ≫ snd _ _) ≫ P.inclusion.hom.hom)) ≫ Q.projection =
    (b₀ * ((b ≫ snd _ _) ≫ P.inclusion.hom.hom)) ≫ Q.projection at h
  rw [quotient_rightMul Q a₀ (a ≫ snd _ _), quotient_rightMul Q b₀ (b ≫ snd _ _)] at h
  have h' := congrArg (quotientAct Q ((b ≫ fst _ _ ≫ P.inclusion.hom.hom)⁻¹)) h
  rw [quotientAct_projection, quotientAct_projection] at h'
  dsimp only [a₀, b₀] at h'
  have hTranslate :
      ((p ≫ P.inclusion.hom.hom) * (toUnit Y ≫ g w)) ≫ Q.projection =
        (toUnit Y ≫ g v) ≫ Q.projection := by
    simpa only [quotientAct_projection, p, MonObj.mul_comp, GrpObj.inv_comp, Category.assoc,
      ← mul_assoc, inv_mul_cancel, one_mul] using h'
  have hnorm (s) : Normalizes S.inclusion (g s) := (D.normalizerProperty _ _).2 ⟨n s, rfl⟩
  have hcoset := normalizer_cosets_of_translate D hInt hSP Q c L hc hPL hL
    (hnorm w) (hnorm v) K _ hp hTranslate
  apply hne
  apply labels_eq_of_equal_cosets D hInt Q (Y := Y) (IsLocalRing.closedPoint K) (hn w) (hn v)
  simpa only [g, Category.assoc] using hcoset

private theorem pairwise_rational_cosets {P : ClosedSubgroup G.val} {W : Type u}
    (g : W → (𝟙_ (SchemeOver k) ⟶ G.val.X)) (O : ∀ w, DoubleOrbit P (g w))
    (hO : Pairwise (fun w v ↦ Disjoint (Set.range (O w).inclusion.left)
      (Set.range (O v).inclusion.left))) :
    Pairwise (fun w v ↦ Disjoint (doubleCoset P (𝟙_ (SchemeOver k)) (g w))
      (doubleCoset P (𝟙_ (SchemeOver k)) (g v))) := by
  have hmem (w) (z : 𝟙_ (SchemeOver k) ⟶ G.val.X)
      (hz : z ∈ doubleCoset P (𝟙_ (SchemeOver k)) (g w)) :
      z.left (IsLocalRing.closedPoint k) ∈ Set.range (O w).inclusion.left := by
    rw [range_doubleOrbit]
    obtain ⟨_, h, _, ⟨b, rfl⟩, rfl⟩ := Set.mem_mul.mp hz
    obtain ⟨_, ⟨a, rfl⟩, _, ht, rfl⟩ := Set.mem_mul.mp h
    rw [Set.mem_singleton_iff] at ht
    subst ht
    refine ⟨(lift a b).left (IsLocalRing.closedPoint k), ?_⟩
    have hh := comp_doubleOrbitMap P (g w) (lift a b)
    rw [lift_fst_assoc, lift_snd_assoc] at hh
    exact congrArg (fun f : 𝟙_ (SchemeOver k) ⟶ G.val.X ↦ f.left (IsLocalRing.closedPoint k)) hh
  intro w v hne
  apply Set.disjoint_left.2
  intro z hz hz'
  exact Set.disjoint_left.1 (hO hne) (hmem w z hz) (hmem v z hz')

/-- The relative decomposition with the three frozen upstream statements as explicit premises. -/
theorem relativeBruhat_conditional.{v}
    (common : CommonMaximalSplitTorus.{v})
    (finiteQuotient : FiniteConstantQuotient.{v})
    (weylAction : RelativeWeylAction.{v}) : Statement.{v} := by
  classical
  intro k _ G hG S P hS hP hSP
  obtain ⟨D, hD⟩ := finiteQuotient G hG S hS
  have hInt := hD P hP hSP
  obtain ⟨hZ, e, _, he, hrep, _, _⟩ := weylAction G hG S P hS hP hSP D
  letI := hZ
  refine ⟨D, hZ, e, he, hrep, ?_⟩
  intro n hn
  obtain ⟨⟨Q⟩, hQ⟩ := ProjectiveFlags.smoothProjectiveQuotient k G P hP.1
  have ⟨j, hj⟩ := hSP
  let S' := restrictSubgroup S P j hj
  have hs' : subgroupOfSubgroup P S' = S := compose_restrict S P j hj
  have hS' := maximalSplitInParabolic (P := P) (S := S') (hs'.symm ▸ hS)
  obtain ⟨c, L, hPL, _, _, _, hL⟩ := MaximalSplitTori.minimalParabolicLevi G P hP S' hS'
  let g := fun w ↦ n w ≫ D.normalizer.inclusion.hom.hom
  let O := fun w ↦ Classical.choice (exists_doubleOrbit hP Q (hQ Q).2.1 (g w))
  have hinc : (subgroupOfSubgroup P S').inclusion = S.inclusion := hj
  have hc : c ≫ (subgroupOfSubgroup P S').inclusion = c ≫ S.inclusion :=
    congrArg (c ≫ ·) hinc
  have hLevi : RepresentsSubgroup L.centralizer (fun _ g ↦ Centralizes S.inclusion g) := by
    intro Y g
    exact (Iff.of_eq (congrArg (fun i ↦ Centralizes i g) hinc.symm)).trans (hL Y g)
  have hO := pairwise_orbits D hInt Q hSP c L hc hPL hLevi n hn O
  exact ⟨rational_coverage common hG hS hP hSP D hInt e he n hn,
    pairwise_rational_cosets g O hO, O, hO⟩

end

end LinearAlgebraicGroups.Relative.RelativeBruhat

universe v8_closure_c982facda6f48b3a_u0
theorem _root_.«LinearAlgebraicGroups».«Relative».«RelativeBruhat».«relativeBruhat» : _root_.«LinearAlgebraicGroups».«Specs».«Relative».«RelativeBruhat».«Statement».{v8_closure_c982facda6f48b3a_u0} :=
  @_root_.«LinearAlgebraicGroups».«Relative».«RelativeBruhat».«relativeBruhat_conditional».{v8_closure_c982facda6f48b3a_u0} (@_root_.«LinearAlgebraicGroups».«Relative».«RelativeWeylScheme».«commonMaximalSplitTorus».{v8_closure_c982facda6f48b3a_u0}) (@_root_.«LinearAlgebraicGroups».«Relative».«RelativeWeylScheme».«finiteConstantQuotient».{v8_closure_c982facda6f48b3a_u0}) (@_root_.«LinearAlgebraicGroups».«Relative».«RelativeWeylScheme».«relativeWeylAction».{v8_closure_c982facda6f48b3a_u0})
