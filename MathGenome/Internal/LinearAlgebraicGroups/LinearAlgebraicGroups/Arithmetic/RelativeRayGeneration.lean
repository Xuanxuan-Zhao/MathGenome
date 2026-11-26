import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Arithmetic.RelativeRayGeneration
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.RelativeRootIrreducibility
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Relative.Parabolics
import Batteries.Tactic.OpenPrivate

open AlgebraicGeometry CategoryTheory
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj BigOperators

universe u

namespace LinearAlgebraicGroups.Arithmetic.RelativeRayGeneration

open LinearAlgebraicGroups.Specs
open Specs.Arithmetic.RelativeRayGeneration
open Specs.Arithmetic.RelativeRootIrreducibility (IsAbsolutelyAlmostSimple)
open Specs.BorelProper (IsParabolic)
open Specs.DiagonalizableGroups (diagonalGroup IntegerCharacters)
open Specs.GeometricRadicals (IsSplitTorus)
open Specs.Relative.MaximalSplitTori (IsMaximalSplitTorus)
open Specs.SchemeDerivedGroup (IsSubgroupOf)
open Specs.BorelsAndChambers (contractingSubgroup)
open Specs.CharacterDescent (Character Cocharacter compositionPairing)
open Specs.CharacterPairing (adjointWeightSpace pairing)
open Specs.Relative.RelativeReflections (Datum Root)
open Specs.Relative.RelativeWeylScheme (QuotientData rationalProjection)
open Specs.Arithmetic.RelativeRootIrreducibility (realRoot realRoots RealRootSpan)
open Specs.GeometricBorelConjugacy (subgroupOfSubgroup)
open Specs.GeometricRadicals (IsReductive IsUnipotentRadical)
open Specs.Unipotent (closedSubgroupAlgebraicGroup)
open CocharacterDynamics

open private reductive_of_semisimple conjugate_contracting
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.RelativeRootIrreducibility
open private dense_rationalSectionValues group_integral_of_reductive
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Relative.RationalDensity
open private factorThroughOpen from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Relative.RationalFlagLifting
open private centralizes_iff from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Affine.Stabilizers
open private splitTorusImage from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Relative.MaximalSplitTori
open private multiplicative_group_iso from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Relative.LeviConjugacy
open private maximalSplitTorusAbove from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Relative.RelativeWeylScheme
open private subgroupIso_of_same from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.RootData.RankOneFlag
open private pushSubgroup radical_transport from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.RootData.OrderedRootProducts
open private connected_of_geometricallyConnected isIso_of_closedImmersion_of_differential
  limitLie_weightSpans pairing_one from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.RootData.BorelsAndChambers
open private adjointWeightsInternal from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.RootData.RootGroups
open private splitEndomorphism_ext powerMorphism_eq_zpow mapPoints_identity
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Relative.RelativeReflections
open private GradedContraction GradedContraction.action GradedContraction.zero
  GradedContraction.preserve_mul contraction_of_cocharacter coeff_mul_first
  splitSeries_and_coordinates_of_contraction
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Relative.SplitContractingRadical
open private evalLaurent orbit_eval unitPointHom unitPointHom_apply
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Reductive.CocharacterLimitSubgroups
open private groupPresentation from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Affine.SchemeImageQuotient
open private rationalSourceIso from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Relative.RationalDensity
open private realRoots_eq_range from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.RelativeRootIrreducibility
open LieAlgebrasAndRepresentations (RootConnected)

noncomputable section

set_option linter.style.haveILetI false
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false

variable {k : Type u} [Field k] {G : AffineAlgebraicGroup k}

private abbrev Sections (H : GroupScheme k) := 𝟙_ (SchemeOver k) ⟶ H.X

private abbrev rationalSubgroup (H : ClosedSubgroup G.val) : Subgroup (Sections G.val) :=
  SubgroupSections H (𝟙_ (SchemeOver k))

/-- Over an infinite field, a subgroup of the rational points that contains
the rational points of an open chart through the identity is the whole group. -/
private theorem subgroup_eq_top_of_open_chart [Infinite k]
    (hG : IsReductive G) {X : SchemeOver k} (j : X ⟶ G.val.X)
    (hj : IsOpenImmersion j.left)
    (h1 : ∃ e : 𝟙_ (SchemeOver k) ⟶ X, e ≫ j = 1)
    (B : Subgroup (Sections G.val))
    (hB : ∀ p : 𝟙_ (SchemeOver k) ⟶ X, p ≫ j ∈ B) : B = ⊤ := by
  letI := hj
  letI := group_integral_of_reductive G hG
  have hd := dense_rationalSectionValues (X := G.val.X) (fun a : Sections G.val ↦ a)
    (Relative.RationalDensity.reductiveRationalPointsDense k G hG)
  have hm (g : Sections G.val)
      (hg : g.left (IsLocalRing.closedPoint k) ∈ Set.range j.left) : g ∈ B := by
    obtain ⟨p, hp⟩ := factorThroughOpen j g hg
    exact hp ▸ hB p
  obtain ⟨e, he⟩ := h1
  have hpoint : (1 : Sections G.val).left (IsLocalRing.closedPoint k) ∈ Set.range j.left :=
    ⟨e.left (IsLocalRing.closedPoint k),
      congrArg (fun g : Sections G.val ↦ g.left (IsLocalRing.closedPoint k)) he⟩
  apply top_unique
  intro g _
  let r : G.val.X ⟶ G.val.X := (𝟙 G.val.X) * (toUnit G.val.X ≫ g)
  have hr (p : Sections G.val) : p ≫ r = p * g := by
    dsimp only [r]
    rw [MonObj.comp_mul, Category.comp_id, comp_toUnit_assoc]
    rfl
  let x : (𝟙_ (SchemeOver k)).left := IsLocalRing.closedPoint k
  let O : Set G.val.X.left := Set.range j.left
  have hO : IsOpen O := j.left.isOpenEmbedding.isOpen_range
  have hO' : IsOpen (r.left ⁻¹' O) := hO.preimage r.left.continuous
  have hinv : (r.left ⁻¹' O).Nonempty := by
    refine ⟨(g⁻¹ : Sections G.val).left x, ?_⟩
    change r.left ((g⁻¹ : Sections G.val).left x) ∈ O
    rwa [← Scheme.Hom.comp_apply, ← Over.comp_left, hr, inv_mul_cancel]
  obtain ⟨_, hx, ⟨p, rfl⟩⟩ := hd.inter_open_nonempty _ (hO.inter hO')
    (nonempty_preirreducible_inter hO hO' ⟨_, hpoint⟩ hinv)
  have hp := hm p hx.1
  have hpg : p * g ∈ B := by
    apply hm
    change (p * g).left x ∈ O
    rw [← hr, Over.comp_left, Scheme.Hom.comp_apply]
    exact hx.2
  simpa only [inv_mul_cancel_left] using B.mul_mem (B.inv_mem hp) hpg

private theorem centralizer_normalizes_contracting {c : Cocharacter G.val}
    (D : LimitDecomposition c) :
    rationalSubgroup D.centralizer ≤ Subgroup.normalizer (rationalSubgroup D.contracting : Set (Sections G.val)) := by
  rw [Subgroup.le_normalizer_iff]
  rintro _ ⟨z, rfl⟩ _ ⟨p, rfl⟩
  exact conjugate_contracting D z p

private theorem opposite_centralizes {c : Cocharacter G.val} {X : SchemeOver k}
    {x : X ⟶ G.val.X} (h : Centralizes c x) : Centralizes (oppositeCocharacter c) x := by
  apply (centralizes_iff ..).2
  intro Y a b
  exact (centralizes_iff ..).1 h Y a
    (b ≫ (specGroupMap (Specs.DiagonalizableGroups.groupAlgebraMap k
      (invMonoidHom (α := Specs.DiagonalizableGroups.IntegerCharacters.{u})))).hom.hom)

private theorem centralizer_normalizes_opposite {c : Cocharacter G.val}
    (D : LimitDecomposition c) (E : LimitDecomposition (oppositeCocharacter c)) :
    rationalSubgroup D.centralizer ≤ Subgroup.normalizer (rationalSubgroup E.contracting : Set (Sections G.val)) := by
  intro z hz
  apply centralizer_normalizes_contracting E
  exact (E.centralizer_points _ _).1
    (opposite_centralizes ((D.centralizer_points _ _).2 hz))

private theorem eq_top_of_big_cell [Infinite k] (hG : IsReductive G) {c : Cocharacter G.val}
    (D : LimitDecomposition c) (E : LimitDecomposition (oppositeCocharacter c))
    (B : Subgroup (Sections G.val)) (hD : rationalSubgroup D.contracting ≤ B)
    (hE : rationalSubgroup E.contracting ≤ B) (hZ : rationalSubgroup D.centralizer ≤ B) :
    B = ⊤ := by
  letI := hG.1
  have hj := CocharacterDynamics.bigCell G c D E
  refine subgroup_eq_top_of_open_chart hG _ hj ⟨lift 1 (lift 1 1), ?_⟩ B ?_
  · simp [bigCellMap, multiplyFactors, MonObj.comp_mul]
  · intro p
    let n := p ≫ fst _ _
    let z := (p ≫ snd _ _) ≫ fst _ _
    let a := (p ≫ snd _ _) ≫ snd _ _
    have he : p ≫ bigCellMap D E =
        (n ≫ E.contracting.inclusion.hom.hom) *
          ((z ≫ D.centralizer.inclusion.hom.hom) * (a ≫ D.contracting.inclusion.hom.hom)) := by
      simp only [bigCellMap, multiplyFactors, n, z, a, MonObj.comp_mul, Category.assoc]
    rw [he]
    exact B.mul_mem (hE ⟨n, rfl⟩) (B.mul_mem (hZ ⟨z, rfl⟩) (hD ⟨a, rfl⟩))

/-- The two opposite radicals generate a normal subgroup over an infinite field. -/
theorem twoRadicals_normal [Infinite k] (hG : IsReductive G) {c : Cocharacter G.val}
    (D : LimitDecomposition c) (E : LimitDecomposition (oppositeCocharacter c)) :
    (rationalSubgroup D.contracting ⊔ rationalSubgroup E.contracting).Normal := by
  let H := rationalSubgroup D.contracting ⊔ rationalSubgroup E.contracting
  have hZ : rationalSubgroup D.centralizer ≤ Subgroup.normalizer (H : Set (Sections G.val)) :=
    le_trans (le_inf (centralizer_normalizes_contracting D) (centralizer_normalizes_opposite D E))
      (Subgroup.inf_normalizer_le_normalizer_sup _ _)
  have h : Subgroup.normalizer (H : Set (Sections G.val)) = ⊤ := eq_top_of_big_cell hG D E _ (le_sup_left.trans H.le_normalizer)
    (le_sup_right.trans H.le_normalizer) hZ
  exact Subgroup.normalizer_eq_top_iff.mp h

/-- Together with the common Levi, the two radicals generate all rational points. -/
theorem twoRadicals_sup_centralizer [Infinite k] (hG : IsReductive G) {c : Cocharacter G.val}
    (D : LimitDecomposition c) (E : LimitDecomposition (oppositeCocharacter c)) :
    (rationalSubgroup D.contracting ⊔ rationalSubgroup E.contracting) ⊔
        rationalSubgroup D.centralizer = ⊤ :=
  eq_top_of_big_cell hG D E _ (le_sup_left.trans le_sup_left)
    (le_sup_right.trans le_sup_left) le_sup_right

private theorem cocharacter_in_maximal_split (c : Cocharacter G.val) :
    ∃ (S : ClosedSubgroup G.val) (d : Cocharacter S.group),
      IsMaximalSplitTorus S ∧ d ≫ S.inclusion = c := by
  let e : IntegerCharacters.{u} ≃* Multiplicative ℤ := MulEquiv.ulift
  letI : Group.FG IntegerCharacters.{u} :=
    Group.fg_of_surjective (f := e.symm.toMonoidHom) e.symm.surjective
  let M := diagonalGroup (k := k) IntegerCharacters.{u}
  have hM : IsSplitTorus M.val := ⟨1, multiplicative_group_iso⟩
  obtain ⟨I, p, hI, hp⟩ := splitTorusImage M G hM c
  obtain ⟨S, hS, ⟨j, hj⟩⟩ := maximalSplitTorusAbove G I hI
  exact ⟨S, p ≫ j, hS, by rw [Category.assoc, hj, hp.1]⟩

private theorem cocharacter_parabolic (hG : IsReductive G) (c : Cocharacter G.val)
    (D : LimitDecomposition c) : IsParabolic G D.parabolic := by
  obtain ⟨S, d, hS, rfl⟩ := cocharacter_in_maximal_split c
  exact (Relative.RelativeChambers.limitParabolicThroughSplitTorus G hG S hS.1 d D).1

private theorem rationalSubgroup_le {S T : ClosedSubgroup G.val} (h : IsSubgroupOf S T) :
    rationalSubgroup S ≤ rationalSubgroup T := by
  obtain ⟨f, hf⟩ := h
  rintro _ ⟨p, rfl⟩
  refine ⟨p ≫ f.hom.hom, ?_⟩
  change (p ≫ f.hom.hom) ≫ T.inclusion.hom.hom = p ≫ S.inclusion.hom.hom
  rw [Category.assoc]
  exact congrArg (p ≫ ·) ((Grp.forget (SchemeOver k)).congr_map hf)

private theorem contracting_le_unipotentGenerated (hG : IsReductive G)
    {c : Cocharacter G.val} (D : LimitDecomposition c) :
    rationalSubgroup D.contracting ≤ unipotentGenerated G := by
  let P := D.parabolic
  let U := contractingSubgroup D
  have hP : IsParabolic G P := cocharacter_parabolic hG c D
  have hU : IsUnipotentRadical (closedSubgroupAlgebraicGroup P) U :=
    (Relative.SplitContractingRadical.contractingSubgroupIsRadical G hG c D).1
  have h : IsSubgroupOf D.contracting (subgroupOfSubgroup P U) :=
    ⟨𝟙 _, (Category.id_comp _).trans D.contracting_in_G⟩
  exact (rationalSubgroup_le h).trans (le_iSup_of_le P (le_iSup_of_le hP
    (le_iSup_of_le U (le_iSup_of_le hU le_rfl))))

/-- It is enough to contain the rational points of each contracting subgroup,
since every rational parabolic is defined by a rational cocharacter. -/
private theorem unipotentGenerated_le_of_contracting
    (B : Subgroup (Sections G.val))
    (hB : ∀ (c : Cocharacter G.val) (D : LimitDecomposition c),
      rationalSubgroup D.contracting ≤ B) :
    unipotentGenerated G ≤ B := by
  apply iSup_le
  intro P
  apply iSup_le
  intro hP
  apply iSup_le
  intro U
  apply iSup_le
  intro hU
  obtain ⟨c, D, hPD, _, hRad⟩ := Relative.RationalCocharacter.rationalParabolic G P hP
  obtain ⟨e, he⟩ := subgroupIso_of_same hPD
  let V := pushSubgroup e.symm (contractingSubgroup D)
  have hV : IsUnipotentRadical (closedSubgroupAlgebraicGroup P) V :=
    radical_transport (A := closedSubgroupAlgebraicGroup D.parabolic)
      (B := closedSubgroupAlgebraicGroup P) e.symm (contractingSubgroup D) hRad.1
  obtain ⟨j, hj⟩ := hV.2.2 U hU.1 hU.2.1
  have h : IsSubgroupOf (subgroupOfSubgroup P U) D.contracting := by
    refine ⟨j, ?_⟩
    change j ≫ D.contracting.inclusion = U.inclusion ≫ P.inclusion
    rw [← D.contracting_in_G, ← Category.assoc]
    have hj' : j ≫ (D.contractingToParabolic ≫ e.inv) = U.inclusion := hj
    rw [← hj', ← he]
    simp only [Category.assoc, e.inv_hom_id_assoc]
  exact (rationalSubgroup_le h).trans (hB c D)

theorem twoRadicals_le_unipotentGenerated (hG : IsReductive G)
    {c : Cocharacter G.val} (D : LimitDecomposition c)
    (E : LimitDecomposition (oppositeCocharacter c)) :
    rationalSubgroup D.contracting ⊔ rationalSubgroup E.contracting ≤ unipotentGenerated G :=
  sup_le (contracting_le_unipotentGenerated hG D) (contracting_le_unipotentGenerated hG E)

/-- A cocharacter annihilating all weights is central. The zero-weight
space is the image of the differential of the smooth centralizer. -/
private theorem central_of_zero_pairing (hG : IsReductive G) (S : ClosedSubgroup G.val)
    (hS : IsSplitTorus S.group) (c : Cocharacter S.group)
    (hc : ∀ a : Root S, pairing S.group a.val c = 0) :
    ∀ (X : SchemeOver k) (x : X ⟶ G.val.X), Centralizes (c ≫ S.inclusion) x := by
  classical
  obtain ⟨D⟩ := CocharacterDynamics.existsLimitDecomposition G (c ≫ S.inclusion)
  letI := hG.1
  letI : ConnectedSpace G.val.X.left := connected_of_geometricallyConnected hG.2.1
  have hIso : IsIso D.centralizer.inclusion := by
    apply isIso_of_closedImmersion_of_differential
      (A := closedSubgroupAlgebraicGroup D.centralizer) (B := G)
      D.centralizer.inclusion D.centralizer.isClosedImmersion
      (limitSubgroupsSmooth G _ D).2.2
      (connected_of_geometricallyConnected (geometricallyConnectedLimitSubgroups G _ D).2.2)
      hG.1 (connected_of_geometricallyConnected hG.2.1)
    apply Set.range_eq_univ.mp
    change lieImage D.centralizer = Set.univ
    let s := identityLieStructure G
    letI := s.lieRing
    letI := s.lieAlgebra
    rw [(limitLie_weightSpans G S hS c D s).2]
    suffices htop : (⨆ a : {a : Character S.group // pairing S.group a c = 0},
        adjointWeightSpace S a.val s) = ⊤ by
      rw [htop, Submodule.top_coe]
    apply top_unique
    rw [← (adjointWeightsInternal G S hS s).submodule_iSup_eq_top]
    apply iSup_le
    intro a
    by_cases h : pairing S.group a c = 0
    · exact le_iSup (fun a : {a : Character S.group // pairing S.group a c = 0} ↦
        adjointWeightSpace S a.val s) ⟨a, h⟩
    · have ha : a ≠ 1 := fun he ↦ h (he.symm ▸ pairing_one _ hS c)
      have hz : adjointWeightSpace S a s = ⊥ := by
        by_contra hn
        exact h (hc ⟨a, (RootData.CharacterPairing.absoluteRootWeights S s a).mpr ⟨ha, hn⟩⟩)
      rw [hz]
      exact bot_le
  intro X x
  letI := hIso
  exact (D.centralizer_points _ _).2 ⟨x ≫ (inv D.centralizer.inclusion).hom.hom, by
    rw [Category.assoc]
    change x ≫ (Grp.forget _).map (inv D.centralizer.inclusion ≫ D.centralizer.inclusion) = x
    rw [IsIso.inv_hom_id]
    exact Category.comp_id _⟩

section RootOrbit

variable {S : ClosedSubgroup G.val} [IsCommMonObj S.group.X]
  {Q : QuotientData S} (d : Datum Q)

include d in
private theorem pairing_mul_char (a b : Character S.group) (c : Cocharacter S.group) :
    pairing S.group (a * b) c = pairing S.group a c + pairing S.group b c := by
  rw [← d.pairing_eq, ← d.pairing_eq, ← d.pairing_eq]
  change d.rootDatum.toLinearMap (Additive.ofMul a + Additive.ofMul b) (Additive.ofMul c) = _
  rw [map_add, LinearMap.add_apply]

include d in
private theorem pairing_zpow_char (a : Character S.group) (c : Cocharacter S.group) (n : ℤ) :
    pairing S.group (a ^ n) c = n * pairing S.group a c := by
  rw [← d.pairing_eq, ← d.pairing_eq]
  change d.rootDatum.toLinearMap (n • Additive.ofMul a) (Additive.ofMul c) = _
  rw [map_smul, LinearMap.smul_apply, zsmul_eq_mul]
  rfl

/-- For a nonzero evaluation on an irreducible system, every root has
a Weyl translate with nonzero evaluation. -/
private theorem orbit_detects_root
    [NormedAddCommGroup (RealRootSpan S)] [InnerProductSpace ℝ (RealRootSpan S)]
    (hR : LieAlgebrasAndRepresentations.IsIrreducible (realRoots S))
    (hinj : Function.Injective (Specs.Arithmetic.RelativeRootIrreducibility.realCharacter S))
    (hcartan : ∀ a b : Root S,
      2 * inner ℝ (realRoot b) (realRoot a) / inner ℝ (realRoot a) (realRoot a) =
        (pairing S.group b.val (d.reflection a).coroot : ℝ))
    (c : Cocharacter S.group) (hc : ∃ a : Root S, pairing S.group a.val c ≠ 0)
    (b : Root S) :
    ∃ w : Q.splitImage.labels, pairing S.group (w.val b.val) c ≠ 0 := by
  classical
  let reached (a : Root S) : Prop :=
    ∃ w : Q.splitImage.labels, pairing S.group (w.val a.val) c ≠ 0
  have step (a b : Root S) (hab : inner ℝ (realRoot b) (realRoot a) ≠ 0)
      (ha : reached a) : reached b := by
    by_contra hn
    obtain ⟨w, hw⟩ := ha
    have hzero (w' : Q.splitImage.labels) : pairing S.group (w'.val b.val) c = 0 := by
      by_contra hw'
      exact hn ⟨w', hw'⟩
    have hcoroot : pairing S.group b.val (d.reflection a).coroot ≠ 0 := by
      intro he
      have hx := hcartan a b
      rw [he, Int.cast_zero] at hx
      have hn' : inner ℝ (realRoot a) (realRoot a) ≠ 0 := by
        exact inner_self_ne_zero.mpr (fun h ↦ hab (by rw [h, inner_zero_right]))
      exact (div_ne_zero (mul_ne_zero (by norm_num) hab) hn') hx
    have he := hzero (w * (d.reflection a).label)
    change pairing S.group (w.val ((d.reflection a).label.val b.val)) c = 0 at he
    rw [(d.reflection a).characterFormula, map_mul, map_zpow, pairing_mul_char d,
      pairing_zpow_char d, hzero w, zero_add] at he
    exact (mul_ne_zero (neg_ne_zero.mpr hcoroot) hw) he
  let reaches (x : RealRootSpan S) : Prop := ∃ a : Root S, realRoot a = x ∧ reached a
  have hstep : ∀ x y : RealRootSpan S, x ∈ realRoots S → y ∈ realRoots S →
      inner ℝ x y ≠ 0 → (reaches x ↔ reaches y) := by
    rw [realRoots_eq_range]
    rintro _ _ ⟨a, rfl⟩ ⟨b, rfl⟩ hab
    have hf (a b : Root S) (h : inner ℝ (realRoot b) (realRoot a) ≠ 0) :
        reaches (realRoot a) → reaches (realRoot b) := by
      rintro ⟨x, hx, hx'⟩
      have he : x = a := Subtype.ext (hinj (congrArg Subtype.val hx))
      exact ⟨b, rfl, step a b h (he ▸ hx')⟩
    exact ⟨hf a b (by rwa [real_inner_comm]), hf b a hab⟩
  obtain ⟨a, ha⟩ := hc
  have hconn : RootConnected (realRoots S) (realRoot a) (realRoot b) :=
    hR.2 _ (by rw [realRoots_eq_range]; exact ⟨a, rfl⟩) _
      (by rw [realRoots_eq_range]; exact ⟨b, rfl⟩)
  have htransport : ∀ x y, RootConnected (realRoots S) x y → (reaches x ↔ reaches y) := by
    intro x y hxy
    induction hxy with
    | rel x y h => exact hstep x y h.1 h.2.1 h.2.2
    | refl => rfl
    | symm _ _ _ ih => exact ih.symm
    | trans _ _ _ _ _ ih₁ ih₂ => exact ih₁.trans ih₂
  obtain ⟨x, hx, hx'⟩ := (htransport _ _ hconn).mp ⟨a, rfl, 1, ha⟩
  have he : x = b := Subtype.ext (hinj (congrArg Subtype.val hx))
  exact he ▸ hx'

end RootOrbit

section CentralImage

private abbrev Gm (k : Type u) [Field k] : GroupScheme k :=
  specGroup (Specs.DiagonalizableGroups.groupAlgebra k IntegerCharacters)

private def HasCentralImage (B : Subgroup (Sections G.val)) [B.Normal]
    (c : Cocharacter G.val) : Prop :=
  ∀ x : Sections (Gm k), QuotientGroup.mk' B (x ≫ c.hom.hom) ∈
    Subgroup.center (Sections G.val ⧸ B)

private theorem fixed_cocharacter_central_image [Infinite k] (hG : IsReductive G)
    {c : Cocharacter G.val} (D : LimitDecomposition c)
    (E : LimitDecomposition (oppositeCocharacter c))
    {B : Subgroup (Sections G.val)} [B.Normal]
    (hB : rationalSubgroup D.contracting ⊔ rationalSubgroup E.contracting = B) :
    HasCentralImage B c := by
  intro x
  let q := QuotientGroup.mk' B
  let p := x ≫ c.hom.hom
  let C := (Subgroup.centralizer ({q p} : Set (Sections G.val ⧸ B))).comap q
  have hb : B ≤ C := by
    intro g hg
    change q g ∈ Subgroup.centralizer ({q p} : Set (Sections G.val ⧸ B))
    rw [show q g = 1 from (QuotientGroup.eq_one_iff g).mpr hg]
    exact Subgroup.one_mem _
  have hz : rationalSubgroup D.centralizer ≤ C := by
    intro g hg
    have h := (D.centralizer_points _ _).mpr hg
    have hc : Commute g p := by
      simpa only [Category.id_comp] using (centralizes_iff ..).mp h _ (𝟙 _) x
    change q g ∈ Subgroup.centralizer ({q p} : Set (Sections G.val ⧸ B))
    exact Subgroup.mem_centralizer_singleton_iff.mpr (hc.map q)
  have h : C = ⊤ := by
    apply top_unique
    rw [← twoRadicals_sup_centralizer hG D E, hB]
    exact sup_le hb hz
  apply Subgroup.mem_center_iff.mpr
  intro y
  obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective B y
  have hg : g ∈ C := h.symm ▸ Subgroup.mem_top g
  exact Subgroup.mem_centralizer_singleton_iff.mp hg

private theorem central_image_conjugate {B : Subgroup (Sections G.val)} [B.Normal]
    {c d : Cocharacter G.val} {g : Sections G.val}
    (h : ∀ x : Sections (Gm k),
      x ≫ d.hom.hom = g * (x ≫ c.hom.hom) * g⁻¹) :
    HasCentralImage B c ↔ HasCentralImage B d := by
  have he (x : Sections (Gm k)) :
      QuotientGroup.mk' B (x ≫ d.hom.hom) ∈ Subgroup.center (Sections G.val ⧸ B) ↔
      QuotientGroup.mk' B (x ≫ c.hom.hom) ∈ Subgroup.center (Sections G.val ⧸ B) := by
    rw [h, map_mul, map_mul, map_inv]
    exact (Subgroup.mem_normalizer_iff.mp
      ((Subgroup.center (Sections G.val ⧸ B)).normalizer_eq_top ▸
        (Subgroup.mem_top (QuotientGroup.mk' B g))) _).symm
  exact ⟨fun hc x ↦ (he x).2 (hc x), fun hd x ↦ (he x).1 (hd x)⟩

private def centralCocharacters (B : Subgroup (Sections G.val)) [B.Normal]
    (S : ClosedSubgroup G.val) [IsCommMonObj S.group.X] : Subgroup (Cocharacter S.group) where
  carrier := {c | HasCentralImage B (c ≫ S.inclusion)}
  one_mem' := by
    intro x
    change QuotientGroup.mk' B ((x ≫ (1 : (Gm k).X ⟶ S.group.X)) ≫
      S.inclusion.hom.hom) ∈ Subgroup.center _
    rw [MonObj.comp_one, MonObj.one_comp, map_one]
    exact Subgroup.one_mem _
  mul_mem' {a b} ha hb := by
    intro x
    change QuotientGroup.mk' B ((x ≫ (a.hom.hom * b.hom.hom)) ≫
      S.inclusion.hom.hom) ∈ Subgroup.center _
    rw [MonObj.comp_mul, MonObj.mul_comp, map_mul]
    exact Subgroup.mul_mem _ (ha x) (hb x)
  inv_mem' {a} ha := by
    intro x
    change QuotientGroup.mk' B ((x ≫ a.hom.hom⁻¹) ≫ S.inclusion.hom.hom) ∈ Subgroup.center _
    rw [GrpObj.comp_inv, GrpObj.inv_comp, map_inv]
    exact Subgroup.inv_mem _ (ha x)

private def powerSaturation {A : Type*} [CommGroup A] (K : Subgroup A) : Subgroup A where
  carrier := {x | ∃ m : ℕ, 0 < m ∧ x ^ m ∈ K}
  one_mem' := ⟨1, Nat.one_pos, by simp⟩
  mul_mem' {a b} := by
    rintro ⟨m, hm, ha⟩ ⟨n, hn, hb⟩
    refine ⟨m * n, Nat.mul_pos hm hn, ?_⟩
    rw [mul_pow]
    refine K.mul_mem (by simpa only [pow_mul] using K.pow_mem ha n) ?_
    rw [Nat.mul_comm m n, pow_mul]
    exact K.pow_mem hb m
  inv_mem' := by
    rintro a ⟨m, hm, ha⟩
    exact ⟨m, hm, by simpa only [inv_pow] using K.inv_mem ha⟩

private theorem le_powerSaturation {A : Type*} [CommGroup A] (K : Subgroup A) :
    K ≤ powerSaturation K := fun x hx ↦ ⟨1, Nat.one_pos, by simpa using hx⟩

private theorem mem_powerSaturation_of_pow {A : Type*} [CommGroup A] {K : Subgroup A}
    {a : A} {m : ℕ} (hm : 0 < m) (ha : a ^ m ∈ powerSaturation K) :
    a ∈ powerSaturation K := by
  obtain ⟨n, hn, h⟩ := ha
  exact ⟨m * n, Nat.mul_pos hm hn, by simpa only [pow_mul] using h⟩

private theorem mem_powerSaturation_of_zpow {A : Type*} [CommGroup A] {K : Subgroup A}
    {a : A} {m : ℤ} (hm : m ≠ 0) (ha : a ^ m ∈ K) : a ∈ powerSaturation K := by
  obtain ⟨n, hn | hn⟩ := m.eq_nat_or_neg
  · exact ⟨n, by omega, by simpa only [hn, zpow_natCast] using ha⟩
  · exact ⟨n, by omega, by simpa only [hn, zpow_neg, zpow_natCast, inv_inv] using K.inv_mem ha⟩

end CentralImage

section WeylAveraging

variable {S : ClosedSubgroup G.val} [IsCommMonObj S.group.X] (Q : QuotientData S)

private abbrev inverseWeylCocharacter (w : Q.splitImage.labels) (c : Cocharacter S.group) :
    Cocharacter S.group := c ≫ (Q.splitImage.conjugation w).inv

omit [IsCommMonObj S.group.X] in
private theorem inverseWeylCocharacter_mul (hS : IsSplitTorus S.group)
    (w z : Q.splitImage.labels) (c : Cocharacter S.group) :
    inverseWeylCocharacter Q (w * z) c =
      inverseWeylCocharacter Q z (inverseWeylCocharacter Q w c) := by
  have he : (Q.splitImage.conjugation (w * z)).inv =
      (Q.splitImage.conjugation w).inv ≫ (Q.splitImage.conjugation z).inv := by
    apply splitEndomorphism_ext hS
    intro a
    rw [← Q.splitImage.characterAction, Category.assoc, ← Q.splitImage.characterAction,
      ← Q.splitImage.characterAction]
    rfl
  simp only [inverseWeylCocharacter, he, Category.assoc]

omit [IsCommMonObj S.group.X] in
private theorem inverseWeylCocharacter_one (hS : IsSplitTorus S.group)
    (c : Cocharacter S.group) : inverseWeylCocharacter Q 1 c = c := by
  have h : (Q.splitImage.conjugation 1).inv = 𝟙 S.group := by
    apply splitEndomorphism_ext hS
    intro a
    rw [Category.id_comp, ← Q.splitImage.characterAction]
    rfl
  simp only [inverseWeylCocharacter, h, Category.comp_id]

omit [IsCommMonObj S.group.X] in
private theorem inverseWeylCocharacter_pairing (w : Q.splitImage.labels) (a : Character S.group)
    (c : Cocharacter S.group) :
    pairing S.group a (inverseWeylCocharacter Q w c) = pairing S.group (w.val a) c := by
  rw [Q.splitImage.characterAction]
  unfold pairing compositionPairing
  simp only [inverseWeylCocharacter, Category.assoc]

private def underlyingCocharacter (T : GroupScheme k) [IsCommMonObj T.X] :
    Cocharacter T →* ((Gm k).X ⟶ T.X) where
  toFun f := f.hom.hom
  map_one' := rfl
  map_mul' := fun _ _ ↦ rfl

private theorem coroot_power_eq_quotient (d : Datum Q) (a : Root S)
    (b : Cocharacter S.group) :
    (d.reflection a).coroot ^ pairing S.group a.val b =
      b / inverseWeylCocharacter Q (d.reflection a).label b := by
  let r := d.reflection a
  let e := Q.splitImage.conjugation r.label
  have hInv : e.hom = e.inv :=
    (cancel_mono e.hom).mp (r.schemeInvolution.trans e.inv_hom_id.symm)
  have hPair : b ≫ a.val = (𝟙 (Gm k) : Character (Gm k)) ^ pairing S.group a.val b :=
    ((RootData.CharacterPairing.characterPairingComposition S.group a.val b).1 _).mpr rfl
      |>.trans (powerMorphism_eq_zpow _)
  have h1 : b ≫ a.val ≫ r.coroot = r.coroot ^ pairing S.group a.val b := by
    rw [← Category.assoc, hPair]
    apply Grp.hom_ext
    rw [Grp.comp_hom_hom]
    change underlyingCocharacter _ (_ ^ _) ≫ r.coroot.hom.hom =
      underlyingCocharacter _ (_ ^ _)
    rw [map_zpow, map_zpow]
    change ((𝟙 (Gm k).X) ^ pairing S.group a.val b) ≫ r.coroot.hom.hom = _
    rw [GrpObj.zpow_comp, Category.id_comp]
    rfl
  have h2 : b ≫ a.val ≫ r.coroot = b / inverseWeylCocharacter Q r.label b := by
    apply Grp.hom_ext
    change b.hom.hom ≫ (a.val ≫ r.coroot).hom.hom =
      b.hom.hom * (b.hom.hom ≫ e.inv.hom.hom)⁻¹
    rw [r.factorization, MonObj.comp_mul, GrpObj.comp_inv, Category.comp_id, hInv]
  exact h1.symm.trans h2

private theorem reflection_inverts_root (d : Datum Q) (a : Root S) :
    (d.reflection a).label.val a.val = a.val⁻¹ := by
  rw [(d.reflection a).characterFormula, (d.reflection a).rootPairing]
  group

private theorem centralCocharacters_inverseWeyl (B : Subgroup (Sections G.val)) [B.Normal]
    (hQ : ∀ w : Q.splitImage.labels, ∃ n, rationalProjection Q n =
      Q.splitImage.constantGroup.sectionPoint w)
    (w : Q.splitImage.labels) (c : Cocharacter S.group) :
    inverseWeylCocharacter Q w c ∈ centralCocharacters B S ↔ c ∈ centralCocharacters B S := by
  obtain ⟨n, hn⟩ := hQ w
  let g : Sections G.val := n ≫ Q.normalizer.inclusion.hom.hom
  let e := Q.splitImage.conjugation w
  have hq : n ≫ Q.projection.hom.hom =
      toUnit (𝟙_ (SchemeOver k)) ≫ Q.splitImage.constantGroup.sectionPoint w := by
    change rationalProjection Q n = _
    rw [show toUnit (𝟙_ (SchemeOver k)) = 𝟙 _ from toUnit_unique _ _, Category.id_comp]
    exact hn
  have he := Q.splitImage.conjugates _ n w hq
  apply central_image_conjugate (B := B) (g := g)
  intro x
  let l := lift (x ≫ (c ≫ e.inv).hom.hom) (𝟙 (𝟙_ (SchemeOver k)))
  have hf := congrArg (l ≫ ·) he
  simp only [conjugateFamily, MonObj.comp_mul, GrpObj.comp_inv, l,
    lift_fst_assoc, lift_snd_assoc, Category.id_comp] at hf
  change g * (x ≫ (c ≫ e.inv).hom.hom ≫ S.inclusion.hom.hom) * g⁻¹ =
    x ≫ (c ≫ e.inv).hom.hom ≫ (e.hom ≫ S.inclusion).hom.hom at hf
  simp only [Grp.comp_hom_hom, Category.assoc] at hf ⊢
  have he' : e.inv.hom.hom ≫ e.hom.hom.hom = 𝟙 S.group.X := by
    rw [← Grp.comp_hom_hom, e.inv_hom_id]
    rfl
  rw [← Category.assoc e.inv.hom.hom, he', Category.id_comp] at hf
  exact hf.symm

private theorem pairing_average_eq_zero (d : Datum Q) (c : Cocharacter S.group)
    (a : Root S) [Fintype Q.splitImage.labels] :
    pairing S.group a.val (∏ w : Q.splitImage.labels, inverseWeylCocharacter Q w c) = 0 := by
  let p := (d.rootDatum.toLinearMap (Additive.ofMul a.val)).toAddMonoidHom.toMultiplicative
  have hp (x : Cocharacter S.group) : (p x).toAdd = pairing S.group a.val x :=
    d.pairing_eq _ _
  have he :
      pairing S.group a.val (∏ w : Q.splitImage.labels, inverseWeylCocharacter Q w c) =
        ∑ w : Q.splitImage.labels, pairing S.group (w.val a.val) c := by
    rw [← hp, map_prod]
    change (∑ w : Q.splitImage.labels, (p (inverseWeylCocharacter Q w c)).toAdd) = _
    simp only [hp, inverseWeylCocharacter_pairing]
  rw [he]
  let f (w : Q.splitImage.labels) := pairing S.group (w.val a.val) c
  have hsum : ∑ w, f w = ∑ w, -f w := by
    apply Fintype.sum_equiv (Equiv.mulRight (d.reflection a).label)
    intro w
    change pairing S.group (w.val a.val) c =
      -pairing S.group (w.val ((d.reflection a).label.val a.val)) c
    rw [reflection_inverts_root Q d, map_inv, ← zpow_neg_one, pairing_zpow_char d]
    ring
  rw [Finset.sum_neg_distrib] at hsum
  change ∑ w, f w = 0
  omega

private theorem centralCocharacters_powerSaturation_eq_top
    (hG : IsReductive G) (hS : IsSplitTorus S.group)
    (d : Datum Q) (B : Subgroup (Sections G.val)) [B.Normal]
    (hQ : ∀ w : Q.splitImage.labels, ∃ n, rationalProjection Q n =
      Q.splitImage.constantGroup.sectionPoint w)
    (c : Cocharacter S.group) (hc : c ∈ centralCocharacters B S)
    (hdetect : ∀ a : Root S, ∃ w : Q.splitImage.labels, pairing S.group (w.val a.val) c ≠ 0) :
    powerSaturation (centralCocharacters B S) = ⊤ := by
  classical
  letI := Q.splitImage.finite
  letI := Fintype.ofFinite Q.splitImage.labels
  let K := centralCocharacters B S
  let K' := powerSaturation K
  have hCoroot (a : Root S) : (d.reflection a).coroot ∈ K' := by
    obtain ⟨w, hw⟩ := hdetect a
    let b := inverseWeylCocharacter Q w c
    have hb : b ∈ K := (centralCocharacters_inverseWeyl Q B hQ w c).2 hc
    apply mem_powerSaturation_of_zpow (m := pairing S.group a.val b)
      ((inverseWeylCocharacter_pairing Q w a.val c).symm ▸ hw)
    rw [coroot_power_eq_quotient Q d]
    exact K.div_mem hb ((centralCocharacters_inverseWeyl Q B hQ _ b).2 hb)
  let L : Subgroup Q.splitImage.labels :=
    { carrier := {w | ∀ b : Cocharacter S.group, b / inverseWeylCocharacter Q w b ∈ K'}
      one_mem' := by
        intro b
        rw [inverseWeylCocharacter_one Q hS]
        simpa only [div_self'] using K'.one_mem
      mul_mem' := fun {w z} hw hz b ↦ by
        rw [inverseWeylCocharacter_mul Q hS]
        have h := K'.mul_mem (hw b) (hz (inverseWeylCocharacter Q w b))
        rwa [div_mul_div_cancel] at h
      inv_mem' := fun {w} hw b ↦ by
        have h := K'.inv_mem (hw (inverseWeylCocharacter Q w⁻¹ b))
        rw [← inverseWeylCocharacter_mul Q hS, inv_mul_cancel,
          inverseWeylCocharacter_one Q hS, inv_div] at h
        exact h }
  have hL : L = ⊤ := by
    apply top_unique
    rw [← d.generates]
    rw [Subgroup.closure_le]
    rintro w ⟨a, rfl⟩ b
    rw [← coroot_power_eq_quotient Q d]
    exact K'.zpow_mem (hCoroot a) _
  apply top_unique
  intro b _
  have hDiff (w : Q.splitImage.labels) : b / inverseWeylCocharacter Q w b ∈ K' :=
    (show w ∈ L from hL.symm ▸ Subgroup.mem_top w) b
  let avg := ∏ w : Q.splitImage.labels, inverseWeylCocharacter Q w b
  have hAvg : avg ∈ K := by
    intro x
    apply Subgroup.mem_center_iff.mpr
    intro y
    obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective B y
    rw [← map_mul, ← map_mul]
    exact congrArg (QuotientGroup.mk' B) (by
      have he := central_of_zero_pairing hG S hS avg (fun a ↦ pairing_average_eq_zero Q d b a) _ g
      simpa only [Category.id_comp] using ((centralizes_iff ..).mp he _ (𝟙 _) x).eq)
  have hprod := K'.prod_mem (t := Finset.univ) fun w _ ↦ hDiff w
  rw [Finset.prod_div_distrib, Finset.prod_const, Finset.card_univ] at hprod
  change b ^ Fintype.card Q.splitImage.labels / avg ∈ K' at hprod
  apply mem_powerSaturation_of_pow (Fintype.card_pos (α := Q.splitImage.labels))
  simpa only [div_mul_cancel] using K'.mul_mem hprod (le_powerSaturation K hAvg)

end WeylAveraging

section ContractingCommutators

open WithConv
open scoped TensorProduct

variable {A : HopfAlgebraCategory k}

private abbrev AlgebraPoint (A : HopfAlgebraCategory k) (R : TestAlgebra k) :=
  (convolutionPoints A).obj R

private def contractedMap (g : GradedContraction A) (R : TestAlgebra k) :
    AlgebraPoint A R →* AlgebraPoint A (polynomialAlgebra R) where
  toFun x := toConv ((Polynomial.mapAlgHom x.ofConv).comp (GradedContraction.action g))
  map_one' := by
    let x : AlgebraPoint A (polynomialAlgebra R) :=
      toConv ((Polynomial.mapAlgHom (1 : AlgebraPoint A R).ofConv).comp
        (GradedContraction.action g))
    have h : x = x * x := by
      simpa only [mul_one] using GradedContraction.preserve_mul g R 1 1
    exact mul_left_cancel (h.symm.trans (mul_one x).symm)
  map_mul' := GradedContraction.preserve_mul g R

private def polynomialPointCoordinates (E : MvPolynomial (Fin n) k ≃ₐ[k] A)
    (R : TestAlgebra k) : AlgebraPoint A R ≃ (Fin n → R) where
  toFun x i := x.ofConv (E (MvPolynomial.X i))
  invFun v := toConv ((MvPolynomial.aeval v).comp E.symm.toAlgHom)
  left_inv x := by
    apply WithConv.ofConv_injective
    apply AlgHom.ext
    intro a
    obtain ⟨p, rfl⟩ := E.surjective a
    change MvPolynomial.aeval (fun i ↦ x.ofConv (E (MvPolynomial.X i))) (E.symm (E p)) =
      x.ofConv (E p)
    rw [E.symm_apply_apply]
    have h : MvPolynomial.aeval (fun i ↦ x.ofConv (E (MvPolynomial.X i))) = x.ofConv.comp E.toAlgHom :=
      MvPolynomial.algHom_ext (fun i ↦ MvPolynomial.aeval_X _ _)
    exact DFunLike.congr_fun h p
  right_inv v := by
    funext i
    change MvPolynomial.aeval v (E.symm (E (MvPolynomial.X i))) = v i
    rw [E.symm_apply_apply, MvPolynomial.aeval_X]

variable {n : ℕ} (E : MvPolynomial (Fin n) k ≃ₐ[k] A) (w : Fin n → ℕ)
  (g : GradedContraction A)
  (hmono : ∀ i, GradedContraction.action g (E (MvPolynomial.X i)) =
    Polynomial.monomial (w i) (E (MvPolynomial.X i)))
  (hε : ∀ i, Bialgebra.counitAlgHom k A (E (MvPolynomial.X i)) = 0)

include hmono in
private theorem contractedMap_coordinate (R : TestAlgebra k) (x : AlgebraPoint A R) (i : Fin n) :
    polynomialPointCoordinates E _ (contractedMap g R x) i =
      Polynomial.monomial (w i) (polynomialPointCoordinates E R x i) := by
  change Polynomial.map x.ofConv.toRingHom (GradedContraction.action g (E (MvPolynomial.X i))) = _
  rw [hmono, Polynomial.map_monomial]
  rfl

include hε in
private theorem polynomialPointCoordinates_one (R : TestAlgebra k) (i : Fin n) :
    polynomialPointCoordinates E R (1 : AlgebraPoint A R) i = 0 := by
  change algebraMap k R (Bialgebra.counitAlgHom k A (E (MvPolynomial.X i))) = 0
  rw [hε, map_zero]

private abbrev truncatedAlgebra (R : TestAlgebra k) (d : ℕ) : TestAlgebra k :=
  CommAlgCat.of k (Polynomial R ⧸ Ideal.span ({(Polynomial.X : Polynomial R) ^ d} : Set _))

private def truncateMap (R : TestAlgebra k) (d : ℕ) :
    polynomialAlgebra R ⟶ truncatedAlgebra R d :=
  CommAlgCat.ofHom (Ideal.Quotient.mkₐ k
    (Ideal.span ({(Polynomial.X : Polynomial R) ^ d} : Set (Polynomial R))))

private def contractionFiltration (g : GradedContraction A) (R : TestAlgebra k) (d : ℕ) :
    Subgroup (AlgebraPoint A R) :=
  (((convolutionPoints A).map (truncateMap R d)).hom.comp (contractedMap g R)).ker

include hmono hε in
private theorem mem_contractionFiltration (R : TestAlgebra k) (d : ℕ) (x : AlgebraPoint A R) :
    x ∈ contractionFiltration g R d ↔
      ∀ i, w i < d → polynomialPointCoordinates E R x i = 0 := by
  let Q := truncatedAlgebra R d
  change (((convolutionPoints A).map (truncateMap R d)).hom (contractedMap g R x) :
    AlgebraPoint A Q) = 1 ↔ _
  rw [← (polynomialPointCoordinates E Q).injective.eq_iff, funext_iff]
  apply forall_congr'
  intro i
  rw [polynomialPointCoordinates_one E hε]
  have h : polynomialPointCoordinates E Q
        (((convolutionPoints A).map (truncateMap R d)).hom (contractedMap g R x)) i =
        (truncateMap R d).hom (Polynomial.monomial (w i)
          (polynomialPointCoordinates E R x i)) := by
    change (truncateMap R d).hom (polynomialPointCoordinates E _ (contractedMap g R x) i) = _
    rw [contractedMap_coordinate E w g hmono]
  rw [h]
  change Ideal.Quotient.mk _ _ = 0 ↔ _
  rw [Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton, Polynomial.X_pow_dvd_iff]
  constructor
  · intro h hi
    simpa only [Polynomial.coeff_monomial, ite_true] using h (w i) hi
  · intro h j hj
    by_cases he : j = w i
    · subst j
      simp only [Polynomial.coeff_monomial, ite_true, h hj]
    · simp only [Polynomial.coeff_monomial, ite_eq_right (Ne.symm he)]

private theorem low_coefficients_zero (R : TestAlgebra k) (d : ℕ)
    (x : AlgebraPoint A R) (hx : x ∈ contractionFiltration g R d)
    (a : A) (i : ℕ) (hi : 0 < i) (hid : i < d) :
    ((contractedMap g R x).ofConv a).coeff i = 0 := by
  have h := congrArg (fun v : AlgebraPoint A (truncatedAlgebra R d) ↦ v.ofConv a)
    (show ((convolutionPoints A).map (truncateMap R d)).hom (contractedMap g R x) = 1 from hx)
  have he : Ideal.Quotient.mk (Ideal.span ({(Polynomial.X : Polynomial R) ^ d} :
        Set (Polynomial R))) ((contractedMap g R x).ofConv a - Polynomial.C
          (algebraMap k R (Coalgebra.counit (R := k) a))) = 0 := by
      rw [map_sub, sub_eq_zero]
      exact h
  rw [Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton, Polynomial.X_pow_dvd_iff] at he
  simpa only [Polynomial.coeff_sub, Polynomial.coeff_C, ite_eq_right hi.ne', sub_zero] using he i hid

private theorem contractedCoefficient_mul (R : TestAlgebra k) (d : ℕ) (hd : 0 < d)
    (x y : AlgebraPoint A R) (hx : x ∈ contractionFiltration g R d)
    (hy : y ∈ contractionFiltration g R d) (a : A) :
    ((contractedMap g R (x * y)).ofConv a).coeff d =
      ((contractedMap g R x).ofConv a).coeff d + ((contractedMap g R y).ofConv a).coeff d := by
  let p := contractedMap g R
  have h0 (f : AlgebraPoint A R) (b : A) :
      ((p f).ofConv b).coeff 0 = algebraMap k R (Coalgebra.counit (R := k) b) := by
    change (Polynomial.map f.ofConv.toRingHom (GradedContraction.action g b)).coeff 0 = _
    rw [Polynomial.coeff_map, GradedContraction.zero g]
    exact f.ofConv.commutes _
  let l (v v' : AlgebraPoint A (polynomialAlgebra R)) :=
    Algebra.TensorProduct.lift v.ofConv v'.ofConv (fun _ _ ↦ .all _ _)
  have ht (t : A ⊗[k] A) :
      (l (p x) (p y) t).coeff d = (l (p x) 1 t).coeff d + (l 1 (p y) t).coeff d := by
    induction t using TensorProduct.inductionOn with
    | tmul b c =>
      simp only [l, Algebra.TensorProduct.lift_tmul]
      rw [coeff_mul_first d hd
        (fun i hi hj ↦ low_coefficients_zero g R d x hx b i hi hj)
        (fun i hi hj ↦ low_coefficients_zero g R d y hy c i hi hj)]
      change _ = ((p x).ofConv b * Polynomial.C (algebraMap k R
        (Coalgebra.counit (R := k) c))).coeff d +
          (Polynomial.C (algebraMap k R (Coalgebra.counit (R := k) b)) *
            (p y).ofConv c).coeff d
      rw [Polynomial.coeff_mul_C, Polynomial.coeff_C_mul, h0, h0, add_comm]
    | add t s ht hs =>
      simp only [map_add, Polynomial.coeff_add, ht, hs]
      abel
  change ((p (x * y)).ofConv a).coeff d = _
  rw [map_mul]
  have hc (v v' : AlgebraPoint A (polynomialAlgebra R)) :
      (v * v').ofConv a = l v v' (Coalgebra.comul (R := k) a) :=
    AlgHom.convMul_apply v v' a
  have he : ((p x * p y).ofConv a).coeff d =
      ((p x * 1).ofConv a).coeff d + ((1 * p y).ofConv a).coeff d := by
    rw [hc, hc, hc]
    exact ht _
  simpa only [mul_one, one_mul] using he

include hmono in
private theorem filtration_coordinate_mul (R : TestAlgebra k)
    (x y : AlgebraPoint A R) (i : Fin n) (hi : 0 < w i)
    (hx : x ∈ contractionFiltration g R (w i))
    (hy : y ∈ contractionFiltration g R (w i)) :
    polynomialPointCoordinates E R (x * y) i =
      polynomialPointCoordinates E R x i + polynomialPointCoordinates E R y i := by
  have he := contractedCoefficient_mul g R (w i) hi x y hx hy (E (MvPolynomial.X i))
  change (polynomialPointCoordinates E _ (contractedMap g R (x * y)) i).coeff (w i) =
    (polynomialPointCoordinates E _ (contractedMap g R x) i).coeff (w i) +
      (polynomialPointCoordinates E _ (contractedMap g R y) i).coeff (w i) at he
  simpa only [contractedMap_coordinate E w g hmono, Polynomial.coeff_monomial,
    ite_true] using he

private def scalingMap (g : GradedContraction A) (R : TestAlgebra k) (t : R) :
    AlgebraPoint A R →* AlgebraPoint A R :=
  ((convolutionPoints A).map (polynomialEvaluate R t)).hom.comp (contractedMap g R)

include hmono in
private theorem scalingMap_coordinate (R : TestAlgebra k) (t : R)
    (x : AlgebraPoint A R) (i : Fin n) :
    polynomialPointCoordinates E R (scalingMap g R t x) i =
      polynomialPointCoordinates E R x i * t ^ w i := by
  change (polynomialEvaluate R t).hom
    (polynomialPointCoordinates E _ (contractedMap g R x) i) = _
  rw [contractedMap_coordinate E w g hmono]
  change (Polynomial.monomial (w i) (polynomialPointCoordinates E R x i)).eval₂
    (RingHom.id R) t = _
  rw [Polynomial.eval₂_monomial, RingHom.id_apply]

include hmono hε in
private theorem scaling_commutator_surjective
    (hw : ∀ i, 0 < w i) (t : k) (ht : ∀ i, t ^ w i ≠ 1)
    (a : AlgebraPoint A (CommAlgCat.of k k)) :
    ∃ x : AlgebraPoint A (CommAlgCat.of k k),
      scalingMap g (CommAlgCat.of k k) t x * x⁻¹ = a := by
  classical
  let R := CommAlgCat.of k k
  let F := contractionFiltration g R
  let s := scalingMap g R t
  let X := polynomialPointCoordinates E R
  have memF (d : ℕ) (x : AlgebraPoint A R) :
      x ∈ F d ↔ ∀ i, w i < d → X x i = 0 :=
    mem_contractionFiltration E w g hmono hε R d x
  have hm (d : ℕ) {x : AlgebraPoint A R} (hx : x ∈ F d) : s x ∈ F d := by
    apply (memF d _).mpr
    intro i hi
    change polynomialPointCoordinates E R (scalingMap g R t x) i = 0
    rw [scalingMap_coordinate E w g hmono, (memF d x).mp hx i hi, zero_mul]
  have hstep (d : ℕ) (b : AlgebraPoint A R) (hb : b ∈ F d) :
      ∃ z : AlgebraPoint A R, (s z)⁻¹ * b * z ∈ F (d + 1) := by
    let v (i : Fin n) := if w i = d then X b i / (t ^ w i - 1) else 0
    let z := X.symm v
    have hz : z ∈ F d := (memF d _).mpr (fun i hi ↦ by
      simp [z, v, ne_of_lt hi])
    have hsz := hm d hz
    have hinv := (F d).inv_mem hsz
    have hpart := (F d).mul_mem hinv hb
    have hres := (F d).mul_mem hpart hz
    refine ⟨z, (memF (d + 1) _).mpr ?_⟩
    intro i hi
    by_cases h : w i < d
    · exact (memF d _).mp hres i h
    have hd : w i = d := by omega
    have hadd {p q : AlgebraPoint A R} (hp : p ∈ F d) (hq : q ∈ F d) :
        X (p * q) i = X p i + X q i :=
      filtration_coordinate_mul E w g hmono R p q i (hw i) (hd.symm ▸ hp) (hd.symm ▸ hq)
    have hneg : X ((s z)⁻¹) i = -(X (s z) i) := by
      have h := hadd hinv hsz
      rw [inv_mul_cancel] at h
      have hone : X (1 : AlgebraPoint A R) i = 0 := polynomialPointCoordinates_one E hε R i
      rw [hone] at h
      exact eq_neg_of_add_eq_zero_right (by simpa only [add_comm] using h.symm)
    have hscale : X (s z) i = X z i * t ^ w i := scalingMap_coordinate E w g hmono R t z i
    have hzval : X z i = X b i / (t ^ w i - 1) := by simp [z, v, hd]
    rw [hadd hpart hz, hadd hinv hb, hneg, hscale, hzval]
    have ht' : t ^ w i - 1 ≠ 0 := sub_ne_zero.mpr (ht i)
    have hcancel (y : k) : -(y / (t ^ w i - 1) * t ^ w i) + y + y / (t ^ w i - 1) = 0 := by
      calc
        _ = y - y / (t ^ w i - 1) * (t ^ w i - 1) := by ring
        _ = 0 := by rw [div_mul_cancel₀ _ ht', sub_self]
    exact hcancel (X b i)
  have hfind (d : ℕ) : ∃ x : AlgebraPoint A R, (s x)⁻¹ * a * x ∈ F d := by
    induction d with
    | zero => exact ⟨1, (memF _ _).mpr (fun i hi ↦ (Nat.not_lt_zero _ hi).elim)⟩
    | succ d ih =>
      obtain ⟨x, hx⟩ := ih
      obtain ⟨z, hz⟩ := hstep d _ hx
      refine ⟨x * z, ?_⟩
      rw [map_mul, mul_inv_rev]
      convert hz using 1
      group
  let bound := (∑ i : Fin n, w i) + 1
  obtain ⟨x, hx⟩ := hfind bound
  have hz : (s x)⁻¹ * a * x = 1 := by
    apply X.injective
    funext i
    have hi : w i < bound := Nat.lt_succ_of_le (Finset.single_le_sum
      (f := w) (fun j _ ↦ Nat.zero_le _) (Finset.mem_univ i))
    have hone : X (1 : AlgebraPoint A R) i = 0 := polynomialPointCoordinates_one E hε R i
    rw [(memF _ _).mp hx i hi, hone]
  refine ⟨x, ?_⟩
  calc
    s x * x⁻¹ = s x * ((s x)⁻¹ * a * x) * x⁻¹ := by rw [hz, mul_one]
    _ = a := by group

end ContractingCommutators

open Specs.AdjointRepresentation (GroupPoints)
open WithConv

private def testPointSections (H : GroupScheme k) :
    GroupPoints H (CommAlgCat.of k k) ≃* Sections H where
  toFun x := (rationalSourceIso k).hom ≫ x
  invFun x := (rationalSourceIso k).inv ≫ x
  left_inv x := (rationalSourceIso k).inv_hom_id_assoc x
  right_inv x := (rationalSourceIso k).hom_inv_id_assoc x
  map_mul' x y := MonObj.comp_mul ((rationalSourceIso k).hom) x y

private theorem exists_good_scaling [Infinite k] {n : ℕ} (w : Fin n → ℕ)
    (hw : ∀ i, 0 < w i) {m : ℕ} (hm : 0 < m) :
    ∃ s : kˣ, ∀ i, ((s ^ m : kˣ) : k) ^ w i ≠ 1 := by
  classical
  let p : Polynomial k := Polynomial.X * ∏ i : Fin n, (Polynomial.X ^ (m * w i) - 1)
  have hp : p ≠ 0 := mul_ne_zero Polynomial.X_ne_zero (Finset.prod_ne_zero_iff.mpr fun i _ ↦ by
    simpa only [Polynomial.C_1] using Polynomial.X_pow_sub_C_ne_zero (Nat.mul_pos hm (hw i)) (1 : k))
  obtain ⟨t, ht⟩ := Infinite.exists_notMem_finset p.roots.toFinset
  have hEval : p.eval t ≠ 0 := by
    intro he
    exact ht (Multiset.mem_toFinset.mpr ((Polynomial.mem_roots hp).mpr he))
  have hne : t ≠ 0 := by
    intro hz
    exact hEval (by simp [p, Polynomial.eval_mul, Polynomial.eval_X, hz])
  refine ⟨Units.mk0 t hne, fun i hi ↦ hEval ?_⟩
  have hx : t ^ (m * w i) - 1 = 0 := by
    simpa only [Units.val_pow_eq_pow_val, Units.val_mk0, pow_mul, sub_eq_zero] using hi
  have hZero : (∏ j : Fin n, (t ^ (m * w j) - 1)) = 0 :=
    Finset.prod_eq_zero (Finset.mem_univ i) hx
  simp only [p, Polynomial.eval_mul, Polynomial.eval_X, Polynomial.eval_prod,
    Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_one, hZero, mul_zero]

private theorem evaluate_polynomialToLaurent (R : TestAlgebra k) (s : Rˣ) :
    polynomialToLaurent R ≫ evalLaurent (𝟙 R) s = polynomialEvaluate R s := by
  apply CommAlgCat.hom_ext
  apply AlgHom.ext
  intro p
  change LaurentPolynomial.eval₂ (RingHom.id R) s p.toLaurent =
    (Polynomial.aevalTower (AlgHom.id k R) (s : R)) p
  rw [LaurentPolynomial.eval₂_toLaurent]
  rfl

private theorem contracting_le_of_central_powers [Infinite k] (hG : IsReductive G)
    {B : Subgroup (Sections G.val)} [B.Normal]
    (c : Cocharacter G.val) (D : LimitDecomposition c) {m : ℕ} (hm : 0 < m)
    (hc : ∀ x : Sections (Gm k), QuotientGroup.mk' B ((x ^ m) ≫ c.hom.hom) ∈
      Subgroup.center (Sections G.val ⧸ B)) :
    rationalSubgroup D.contracting ≤ B := by
  obtain ⟨A, hA, ⟨e⟩⟩ := groupPresentation (closedSubgroupAlgebraicGroup (G := G) D.contracting)
  letI := hA
  obtain ⟨g, hOrbit⟩ := contraction_of_cocharacter G c D e
  have hs : Smooth (specGroup A).X.hom := by
    letI := hG.1
    let eX : (specGroup A).X ≅ D.contracting.group.X := (Grp.forget (SchemeOver k)).mapIso e
    letI : IsIso eX.hom.left := (Over.forget _).map_isIso eX.hom
    letI := (limitSubgroupsSmooth G c D).2.1
    rw [← Over.w eX.hom]
    infer_instance
  obtain ⟨n, w, E, hE⟩ := (splitSeries_and_coordinates_of_contraction g hs).2
  have hε (i : Fin n) : Bialgebra.counitAlgHom k A (E (MvPolynomial.X i)) = 0 := by
    have h := congrArg (fun p : Polynomial A ↦ p.coeff 0) (hE i).2
    change (GradedContraction.action g (E (MvPolynomial.X i))).coeff 0 = _ at h
    rw [GradedContraction.zero, Polynomial.coeff_monomial, ite_eq_right (hE i).1.ne'] at h
    have hh := congrArg (Bialgebra.counitAlgHom k A) h
    rw [(Bialgebra.counitAlgHom k A).commutes, map_zero] at hh
    exact hh
  obtain ⟨s, hScale⟩ := exists_good_scaling (k := k) w (fun i ↦ (hE i).1) hm
  let R := CommAlgCat.of k k
  let s' : Rˣ := (s ^ m : kˣ)
  let J := hopfSpecPointIso A ≪≫ (groupPointsFunctor k).mapIso e
  let f (S : TestAlgebra k) := (J.app S).groupIsoToMulEquiv
  let inc (S : TestAlgebra k) := IsMonHom.monoidHom D.contracting.inclusion.hom.hom
    ((testSpec k).obj (Opposite.op S))
  let F (S : TestAlgebra k) : AlgebraPoint A S →* GroupPoints G.val S :=
    (inc S).comp (f S).toMonoidHom
  have hF (S : TestAlgebra k) (x : AlgebraPoint A S) :
      F S x = (testSpec k).map (CommAlgCat.ofHom x.ofConv).op ≫
        (e.hom ≫ D.contracting.inclusion).hom.hom := rfl
  have hNatural {S T : TestAlgebra k} (a : S ⟶ T) (x : AlgebraPoint A S) :
      F T (((convolutionPoints A).map a).hom x) = mapPoints a (F S x) := by
    rw [hF, hF]
    change (testSpec k).map ((CommAlgCat.ofHom x.ofConv) ≫ a).op ≫ _ =
      (testSpec k).map a.op ≫ (testSpec k).map (CommAlgCat.ofHom x.ofConv).op ≫ _
    simp only [op_comp, Functor.map_comp, Category.assoc]
  have hConj (x : AlgebraPoint A R) :
      F R (scalingMap g R s' x) =
        cocharacterPoint c R s' * F R x * (cocharacterPoint c R s')⁻¹ := by
    have hOrb : mapPoints (polynomialToLaurent R)
        (F (polynomialAlgebra R) (contractedMap g R x)) = orbit c (F R x) := by
      rw [hF, hF]
      exact hOrbit R x.ofConv
    have h := congrArg (mapPoints (X := G.val.X) (evalLaurent (𝟙 R) s')) hOrb
    rw [← mapPoints_comp, evaluate_polynomialToLaurent, orbit_eval] at h
    change F R (((convolutionPoints A).map (polynomialEvaluate R s')).hom
      (contractedMap g R x)) = _
    rw [mapPoints_identity (X := G.val.X) (F R x)] at h
    rw [hNatural]
    exact h
  have central :
      QuotientGroup.mk' B (testPointSections G.val (cocharacterPoint c R s')) ∈
        Subgroup.center (Sections G.val ⧸ B) := by
    let z := unitPoint R (show Rˣ from s)
    have hpow : unitPoint R s' = z ^ m := by
      change unitPoint R s' = unitPoint R (show Rˣ from s) ^ m
      simp only [← unitPointHom_apply]
      exact map_pow (unitPointHom R) (show Rˣ from s) m
    have he : testPointSections G.val (cocharacterPoint c R s') =
        ((testPointSections (Gm k) z) ^ m) ≫ c.hom.hom := by
      change (rationalSourceIso k).hom ≫ unitPoint R s' ≫ c.hom.hom = _
      rw [hpow, ← Category.assoc, MonObj.comp_pow]
      rfl
    rw [he]
    exact hc _
  rintro _ ⟨p, rfl⟩
  obtain ⟨a, ha⟩ := ((f R).trans (testPointSections D.contracting.group)).surjective p
  obtain ⟨x, hx⟩ := scaling_commutator_surjective E w g (fun i ↦ (hE i).2) hε
    (fun i ↦ (hE i).1) (s' : k) hScale a
  let ψ := (QuotientGroup.mk' B).comp ((testPointSections G.val).toMonoidHom.comp (F R))
  have hψ : ψ a = 1 := by
    have h := congrArg ψ hx
    rw [map_mul, map_inv] at h
    rw [← h]
    change QuotientGroup.mk' B (testPointSections G.val (F R (scalingMap g R s' x))) * _ = 1
    rw [hConj, map_mul, map_mul, map_inv, map_mul, map_mul, map_inv]
    let u := QuotientGroup.mk' B (testPointSections G.val (cocharacterPoint c R s'))
    have hcomm : Commute u (ψ x) := ((Subgroup.mem_center_iff.mp central (ψ x))).symm
    change u * ψ x * u⁻¹ * (ψ x)⁻¹ = 1
    rw [hcomm.mul_inv_cancel, mul_inv_cancel]
  apply (QuotientGroup.eq_one_iff _).mp
  change QuotientGroup.mk' B (p ≫ D.contracting.inclusion.hom.hom) = 1
  have hp : testPointSections G.val (F R a) = p ≫ D.contracting.inclusion.hom.hom := by
    have ha' : testPointSections D.contracting.group (f R a) = p := ha
    rw [← ha']
    change (rationalSourceIso k).hom ≫ (f R a ≫ D.contracting.inclusion.hom.hom) =
      ((rationalSourceIso k).hom ≫ f R a) ≫ D.contracting.inclusion.hom.hom
    rw [Category.assoc]
  rw [← hp]
  exact hψ

private theorem all_cocharacter_powers_central [Infinite k] (hG : IsReductive G)
    (hA : IsAbsolutelyAlmostSimple G)
    (c : Cocharacter G.val) (hn : ∃ (X : SchemeOver k) (g : X ⟶ G.val.X), ¬ Centralizes c g)
    (B : Subgroup (Sections G.val)) [B.Normal] (hc : HasCentralImage B c) :
    ∀ d : Cocharacter G.val, ∃ m : ℕ, 0 < m ∧
      ∀ x : Sections (Gm k), QuotientGroup.mk' B ((x ^ m) ≫ d.hom.hom) ∈
        Subgroup.center (Sections G.val ⧸ B) := by
  classical
  obtain ⟨S, b, hS, hb⟩ := cocharacter_in_maximal_split c
  have hNon : Specs.Arithmetic.RelativeRootIrreducibility.HasNoncentralCocharacter S :=
    ⟨b, hb.symm ▸ hn⟩
  obtain ⟨form, hf⟩ := RelativeRootIrreducibility.relativeRootIrreducibility G hA S hS hNon
  letI := @InnerProductSpace.Core.toNormedAddCommGroup ℝ (RealRootSpan S) _ _ _ form
  letI := InnerProductSpace.ofCore form.toCore
  obtain ⟨_, hRoot, _, hinj, _, _, ⟨Q, hComm, hD⟩, _⟩ := hf
  letI := hComm
  obtain ⟨datum, _, _, _, hcartan⟩ := hD
  obtain ⟨chamber⟩ := Relative.RelativeReflections.normalizerChambers G hG S hS Q
  obtain ⟨C, hC⟩ := chamber.existsChamber
  obtain ⟨P, hP, hSP, _⟩ := (Relative.RelativeChambers.chamberCorrespondence G hG S hS).1 C hC
  obtain ⟨_, _, _, _, hQ, _⟩ := Relative.RelativeWeylScheme.relativeWeylAction G hG S P hS hP hSP Q
  have hb' : b ∈ centralCocharacters B S := by
    change HasCentralImage B (b ≫ S.inclusion)
    rwa [hb]
  have hbDetect : ∃ a : Root S, pairing S.group a.val b ≠ 0 := by
    by_contra! h
    obtain ⟨X, g, hg⟩ := hn
    apply hg
    rw [← hb]
    exact central_of_zero_pairing hG S hS.1 b h X g
  have hd : ∀ a : Root S, ∃ w : Q.splitImage.labels, pairing S.group (w.val a.val) b ≠ 0 :=
    orbit_detects_root datum hRoot hinj hcartan b hbDetect
  have hSat := centralCocharacters_powerSaturation_eq_top Q hG hS.1 datum B hQ b hb' hd
  intro d
  obtain ⟨T, a, hT, ha⟩ := cocharacter_in_maximal_split d
  obtain ⟨n, e, he⟩ := Relative.MaximalSplitTori.maximalSplitToriConjugate G hG T S hT hS
  let b' := a ≫ e.hom
  have hbSat : b' ∈ powerSaturation (centralCocharacters B S) :=
    hSat.symm ▸ Subgroup.mem_top b'
  obtain ⟨m, hm, hm'⟩ := hbSat
  refine ⟨m, hm, fun x ↦ ?_⟩
  have hPower :
      x ≫ ((b' ^ m) ≫ S.inclusion).hom.hom = (x ^ m) ≫ (b' ≫ S.inclusion).hom.hom := by
    simp only [Grp.comp_hom_hom, ← Category.assoc]
    change (x ≫ underlyingCocharacter _ (b' ^ m)) ≫ S.inclusion.hom.hom = _
    rw [map_pow, MonObj.comp_pow]
    change ((x ≫ b'.hom.hom) ^ m) ≫ S.inclusion.hom.hom = _
    rw [← MonObj.pow_comp x m b'.hom.hom]
  change HasCentralImage B ((b' ^ m) ≫ S.inclusion) at hm'
  have hMem := hm' x
  rw [hPower] at hMem
  have hex : (x ^ m) ≫ (b' ≫ S.inclusion).hom.hom =
      n * ((x ^ m) ≫ d.hom.hom) * n⁻¹ := by
    let p : Sections T.group := (x ^ m) ≫ a.hom.hom
    have hp : p ≫ toUnit T.group.X ≫ n = n := by
      rw [comp_toUnit_assoc, show toUnit (𝟙_ (SchemeOver k)) = 𝟙 _ from toUnit_unique _ _,
        Category.id_comp]
    have hd' : p ≫ T.inclusion.hom.hom = (x ^ m) ≫ d.hom.hom := by
      change ((x ^ m) ≫ a.hom.hom) ≫ T.inclusion.hom.hom = _
      rw [Category.assoc, ← Grp.comp_hom_hom, ha]
    have he' := congrArg (p ≫ ·) he
    change p ≫ (e.hom ≫ S.inclusion).hom.hom =
      p ≫ ((toUnit T.group.X ≫ n) * T.inclusion.hom.hom * (toUnit T.group.X ≫ n)⁻¹) at he'
    rw [MonObj.comp_mul, MonObj.comp_mul, GrpObj.comp_inv, hp, hd'] at he'
    simpa only [b', p, Grp.comp_hom_hom, Category.assoc] using he'
  rw [hex, map_mul, map_mul, map_inv] at hMem
  have hN : (Subgroup.center (Sections G.val ⧸ B)).Normal := inferInstance
  simpa only [mul_assoc, inv_mul_cancel_left, mul_inv_cancel, mul_one] using
    hN.conj_mem _ hMem (QuotientGroup.mk' B n)⁻¹

/-- The two radicals of the fixed noncentral cocharacter generate all
rational parabolic radicals over any infinite ground field. -/
theorem twoRadicalsGenerate : Statement.{u} := by
  intro k _ _ G hA c hn D E
  have hG := reductive_of_semisimple G hA.1
  let B := rationalSubgroup D.contracting ⊔ rationalSubgroup E.contracting
  letI : B.Normal := twoRadicals_normal hG D E
  have hc : HasCentralImage B c := fixed_cocharacter_central_image hG D E rfl
  have hPower := all_cocharacter_powers_central hG hA c hn B hc
  refine le_antisymm (twoRadicals_le_unipotentGenerated hG D E) ?_
  apply unipotentGenerated_le_of_contracting
  intro d F
  obtain ⟨m, hm, hd⟩ := hPower d
  exact contracting_le_of_central_powers hG d F hm hd

end
end LinearAlgebraicGroups.Arithmetic.RelativeRayGeneration
