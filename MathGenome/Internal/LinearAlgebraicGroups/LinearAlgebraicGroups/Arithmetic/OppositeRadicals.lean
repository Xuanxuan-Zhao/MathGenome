import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Arithmetic.OppositeRadicals
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.RelativeRayGeneration
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.ApproximationOfLocalWords
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Relative.SplitContractingRadical
import Batteries.Tactic.OpenPrivate

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

universe u v

namespace LinearAlgebraicGroups.Arithmetic.OppositeRadicals

open _root_.LinearAlgebraicGroups.Specs
open Specs.Arithmetic.OppositeRadicals
open Specs.Arithmetic.RelativeRootIrreducibility (IsAbsolutelyAlmostSimple)
open Specs.Arithmetic.RelativeRayGeneration (unipotentGenerated)
open Specs.BorelProper (IsParabolic)
open Specs.CharacterDescent (Cocharacter)
open Specs.GeometricRadicals
open Specs.IntegralModels (MatrixRealization)
open Specs.RankOneFlag (SameSubgroup)
open Specs.Unipotent (baseChangedAlgebraicGroup closedSubgroupAlgebraicGroup)
open AdelicGroups ApproximationOfLocalWords
open CocharacterDynamics

open private cocharacter_parabolic testPointSections
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.RelativeRayGeneration
open private reductive_of_semisimple
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.RelativeRootIrreducibility
open private gm_baseChange centralizes_precomposeIso
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Reductive.CocharacterLimitSubgroups
open private extendSubgroup limits_subgroups_extend opposite_baseChange
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.RootData.RankOneFlag
open private factor_of_baseChange from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Affine.ClosedSubgroups
open private centralizes_iff mono_over from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Affine.Stabilizers
open private groupPresentation from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Affine.SchemeImageQuotient

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
set_option linter.style.haveILetI false

section AbsoluteSimplicity

open Specs.CharacterDescent (StandardLattice)
open Specs.DiagonalizableGroups (IntegerCharacters diagonalGroup groupAlgebra groupAlgebraMap)
open Specs.GeometricBorelConjugacy (subgroupOfSubgroup)
open Specs.SchemeDerivedGroup (FactorsThrough IsSubgroupOf)
open Specs.FiniteWordClosure (power wordDomain evaluate)

open private groupBaseChangeTower transportSubgroup transport_normal trivial_baseChange_iff
  evaluate_factors_after_baseChange baseChange_dominant
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Reductive.RadicalBaseChange
open private geometricallyMaximal_of_maximal_split connected_of_geometricallyConnected
  splitTorus_baseChange splitTorus_connected reductive_geometricGroup from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.RootData.BorelsAndChambers
open private splitTorusSmooth from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Reductive.WeylScheme
open private closureSubgroupDescends normalUnipotentTrivial
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Relative.ReductiveLieCentralizers
open private conjugates_stable
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.RelativeRootIrreducibility
open private split_of_torus from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Solvable.GeometricTorusSplitting
open private maximalTorus_exists isTorus_of_split from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Descent.FiniteFieldFlags
open private exists_maximal_torus_over isTorus_iff_coordinates inclusion_mono
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Reductive.MaximalToriConjugate
open private torus_commutative from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Reductive.TorusFreeUnipotent
open private splitPresentation from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.RootData.CharacterPairing
open private splitSchemeComparison splitSchemeComparison_naturality
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Relative.RationalCocharacter
open private splitGroupHomEquiv from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Multiplicative.CharacterDescent
open private affine_tensor affine_power from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Solvable.FiniteWordClosure
open private power_geometry from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Solvable.SchemeDerivedGroup
open private smooth_geometricallyIrreducible_tensor geometry_of_smooth_geometricallyIrreducible
  geometricallyIrreducible_of_connected from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Solvable.WordDomainGeometry
open private factor_through_dominant from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.RelativeRootIrreducibility
open private factor_group_through_subgroup from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Reductive.GeometricBorelConjugacy
open private baseChange_conjugation from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Affine.ClosedSubgroups

variable {k L : Type u} [Field k] [Field L] [Algebra k L]

private theorem splitTorus_of_torus [IsAlgClosed k]
    {G : AffineAlgebraicGroup k} (T : ClosedSubgroup G.val) (hT : IsTorus T.group) :
    IsSplitTorus T.group :=
  split_of_torus ((isTorus_iff_coordinates (closedSubgroupAlgebraicGroup T)).mp hT)

private theorem extended_maximal_torus [IsAlgClosed k] {G : AffineAlgebraicGroup k}
    (hG : IsReductive G) (T : ClosedSubgroup G.val) (hT : IsMaximalTorus T) :
    IsMaximalTorus (extendSubgroup L T) := by
  have hTs := splitTorus_of_torus T hT.1
  have hC := Reductive.TorusCentralizer.maximalTorusCentralizer G hG T hT.1
    (geometricallyMaximal_of_maximal_split G T hT hTs)
  obtain ⟨_, hCL⟩ := centralizerSchemeBaseChange k L T.inclusion T hC
  refine ⟨isTorus_of_split (splitTorus_baseChange hTs), ?_⟩
  intro S hS hTS
  obtain ⟨j, hj⟩ := hTS
  letI : IsCommMonObj S.group.X := torus_commutative (closedSubgroupAlgebraicGroup
    (G := baseChangedAlgebraicGroup L G) S) hS
  have hz : Centralizes (extendSubgroup L T).inclusion S.inclusion.hom.hom := by
    apply (centralizes_iff _ _).mpr
    intro X x y
    have h : Commute x (y ≫ j.hom.hom) := mul_comm' _ _
    have hm := h.map (IsMonHom.monoidHom S.inclusion.hom.hom X)
    change Commute (x ≫ S.inclusion.hom.hom) ((y ≫ j.hom.hom) ≫ S.inclusion.hom.hom) at hm
    rw [Category.assoc, show j.hom.hom ≫ S.inclusion.hom.hom =
      (extendSubgroup L T).inclusion.hom.hom from (Grp.forget (SchemeOver L)).congr_map hj] at hm
    exact hm
  obtain ⟨j', hj'⟩ := (hCL _ _).mp hz
  exact factor_group_through_subgroup (extendSubgroup L T) S.inclusion j' hj'

private theorem nontrivial_torus_in_normal [IsAlgClosed k] {G : AffineAlgebraicGroup k}
    (hG : IsReductive G) (N : ClosedSubgroup G.val) (hN : IsSmoothConnectedNormal N)
    (hn : ¬ IsTrivialSubgroup N) :
    ∃ S : ClosedSubgroup N.group, IsTorus S.group ∧ ¬ IsTrivialSubgroup S := by
  classical
  by_contra! h
  apply hn
  apply normalUnipotentTrivial G hG N hN
  apply TorusFreeUnipotent.torusFreeUnipotent (closedSubgroupAlgebraicGroup N) hN.1 hN.2.1
  intro T hT
  obtain ⟨S, e, _⟩ := closureSubgroupDescends T
  have hT' := splitTorus_of_torus (G := GeometricGroup (closedSubgroupAlgebraicGroup N)) T hT
  have hS : IsTorus S.group := by
    obtain ⟨r, ⟨b⟩⟩ := hT'
    exact ⟨AlgebraicClosure k, inferInstance, inferInstance, inferInstance, r, ⟨e ≪≫ b⟩⟩
  obtain ⟨a⟩ := (trivial_baseChange_iff (k := k) (K := AlgebraicClosure k) S.group).mpr (h S hS)
  exact ⟨e.symm ≪≫ a⟩

/-- A homomorphism between split tori is defined by its map on their character lattices. -/
private theorem lift_split_hom {T : GroupScheme k} {M J : Type u} [CommGroup M] [CommGroup J]
    (q : specGroup (groupAlgebra k M) ≅ T)
    (f : specGroup (groupAlgebra L J) ⟶ (groupBaseChange k L).obj T) :
    ∃ d : specGroup (groupAlgebra k J) ⟶ T,
      (splitSchemeComparison (k := k) L J).hom ≫ (groupBaseChange k L).map d = f := by
  let F := groupBaseChange k L
  let e := splitSchemeComparison (k := k) L M
  obtain ⟨b, hb⟩ := (splitGroupHomEquiv (k := L) M J).surjective (f ≫ F.map q.inv ≫ e.inv)
  change specGroupMap (groupAlgebraMap L b) = f ≫ F.map q.inv ≫ e.inv at hb
  refine ⟨specGroupMap (groupAlgebraMap k b) ≫ q.hom, ?_⟩
  rw [Functor.map_comp, ← Category.assoc, ← splitSchemeComparison_naturality L b, hb]
  change f ≫ F.map q.inv ≫ e.inv ≫ e.hom ≫ F.map q.hom = f
  rw [Iso.inv_hom_id_assoc, ← F.map_comp, q.inv_hom_id, F.map_id, Category.comp_id]

private theorem extended_conjugates_factor {G J : GroupScheme k} (d : J ⟶ G)
    (N : ClosedSubgroup ((groupBaseChange k L).obj G)) (hn : IsNormalSubgroup N.inclusion)
    (a : (groupBaseChange k L).obj J ⟶ N.group)
    (ha : a ≫ N.inclusion = (groupBaseChange k L).map d) :
    FactorsThrough N ((baseChange k L).map (subgroupConjugation d)) := by
  let F := baseChange k L
  let e := prodComparisonIso F G.X J.X
  let G' := (groupBaseChange k L).obj G
  let J' := (groupBaseChange k L).obj J
  obtain ⟨t, ht⟩ := normalSubgroup_conjugate_sections hn
    (fst G'.X J'.X) (snd G'.X J'.X ≫ a.hom.hom)
  have ha' : a.hom.hom ≫ N.inclusion.hom.hom = ((groupBaseChange k L).map d).hom.hom :=
    (Grp.forget (SchemeOver L)).congr_map ha
  have ht' : t ≫ N.inclusion.hom.hom = subgroupConjugation ((groupBaseChange k L).map d) := by
    refine ht.trans ?_
    unfold subgroupConjugation
    rw [Category.assoc, ha']
  refine ⟨e.hom ≫ t, ?_⟩
  change (e.hom ≫ t) ≫ N.inclusion.hom.hom = F.map (subgroupConjugation d)
  rw [Category.assoc, ht', ← baseChange_conjugation L d]
  exact e.hom_inv_id_assoc _

/-- The normal closure of a map from a split torus is witnessed by finitely many
products of its conjugates. These products remain dominant after field extension. -/
private theorem normal_subgroup_full_of_extended_split_torus [IsAlgClosed k]
    {G J : AffineAlgebraicGroup k} (hG : IsReductive G) (hJ : IsSplitTorus J.val)
    (simple : ∀ N : ClosedSubgroup G.val, IsSmoothConnectedNormal N →
      IsTrivialSubgroup N ∨ IsIso N.inclusion)
    (d : J.val ⟶ G.val) (N : ClosedSubgroup ((groupBaseChange k L).obj G.val))
    (hn : IsNormalSubgroup N.inclusion)
    (a : (groupBaseChange k L).obj J.val ⟶ N.group)
    (ha : a ≫ N.inclusion = (groupBaseChange k L).map d)
    [Mono ((groupBaseChange k L).map d)]
    (hJnt : ¬ Nonempty (((groupBaseChange k L).obj J.val) ≅ Grp.trivial (SchemeOver L))) :
    IsIso N.inclusion := by
  let F := baseChange k L
  let X := G.val.X ⊗ J.val.X
  let f := subgroupConjugation d
  let x : 𝟙_ (SchemeOver k) ⟶ X := lift 1 1
  have hx : x ≫ f = 1 := by
    simp only [x, f, subgroupConjugation, MonObj.comp_mul, GrpObj.comp_inv, ← Category.assoc,
      lift_fst, lift_snd, MonObj.one_comp, mul_one, inv_one]
  letI : Smooth G.val.X.hom := hG.1
  letI := connected_of_geometricallyConnected hG.2.1
  letI := splitTorusSmooth hJ
  letI := splitTorus_connected hJ
  letI := geometricallyIrreducible_of_connected G
  letI := geometricallyIrreducible_of_connected J
  letI := G.property.1
  letI := J.property.1
  letI := G.property.2.1
  letI := J.property.2.1
  letI := G.property.2.2
  letI := J.property.2.2
  obtain ⟨hxs, hxi⟩ : Smooth X.hom ∧ GeometricallyIrreducible X.hom :=
    smooth_geometricallyIrreducible_tensor _ _
  letI := hxs
  letI := hxi
  have hpow (m : ℕ) : IsIntegral (power X m).left := by
    obtain ⟨hs, hi⟩ := power_geometry X m
    exact (geometry_of_smooth_geometricallyIrreducible (power X m)).2.2
  have hft : LocallyOfFiniteType X.hom := by
    dsimp only [X]
    rw [Over.tensorObj_hom]
    infer_instance
  have hqc : QuasiCompact X.hom := by
    dsimp only [X]
    rw [Over.tensorObj_hom]
    infer_instance
  letI hXa : IsAffine X.left := affine_tensor (A := G.val.X) (B := J.val.X)
  obtain ⟨B, n, w, _, hnormal, hdom, ⟨j, hj⟩, _, hw⟩ :=
    FiniteWordClosure.existsFiniteWordClosure G X f x affine_tensor hft hqc hx hpow
      (conjugates_stable d)
  letI : IsIntegral (wordDomain X n).left := hpow (2 * n)
  letI : IsAffine (wordDomain X n).left := affine_power (X := X) (2 * n)
  letI : IsAffine B.group.X.left := (closedSubgroupAlgebraicGroup (G := G) B).property.1
  letI : LocallyOfFiniteType B.group.X.hom := (closedSubgroupAlgebraicGroup (G := G) B).property.2.1
  letI : IsAffineHom w.left := isAffineHom_of_isAffine w.left
  letI : IsReduced B.group.X.left := IsSchemeTheoreticallyDominant.isReduced w.left
  haveI : IrreducibleSpace B.group.X.left := by
    have h := ((IrreducibleSpace.isIrreducible_univ _).image w.left
      w.left.continuous.continuousOn).closure
    rw [Set.image_univ, w.left.denseRange.closure_eq] at h
    exact (irreducibleSpace_def _).mpr h
  have hBsm : Smooth B.group.X.hom :=
    LinearAlgebraicGroups.smoothOfReducedOverPerfectField k B.group inferInstance
  rcases simple B ⟨hBsm, inferInstance, hnormal⟩ with hb | hb
  · exfalso
    let p : J.val.X ⟶ X := lift 1 (𝟙 _)
    have hp : p ≫ f = d.hom.hom := by
      simp only [p, f, subgroupConjugation, MonObj.comp_mul, GrpObj.comp_inv, ← Category.assoc,
        lift_fst, lift_snd, Category.id_comp, one_mul, inv_one, mul_one]
    obtain ⟨b, hb'⟩ := factor_group_through_subgroup B d (p ≫ j)
      (by rw [Category.assoc, hj, hp])
    have hbL := (trivial_baseChange_iff (k := k) (K := L) B.group).mpr hb
    obtain ⟨e⟩ := hbL
    have hz := (Grp.isZero_trivial (SchemeOver L)).of_iso e
    have hd : (groupBaseChange k L).map d = 0 := by
      rw [← hb', Functor.map_comp, hz.eq_of_tgt ((groupBaseChange k L).map b) 0, zero_comp]
    exact hJnt ⟨(IsZero.of_mono_eq_zero _ hd).iso (Grp.isZero_trivial _)⟩
  · obtain ⟨t, ht⟩ := extended_conjugates_factor d N hn a ha
    have hw' : w ≫ B.inclusion.hom.hom = evaluate f n (𝟙 (wordDomain X n)) :=
      (Category.id_comp _).symm.trans (hw (wordDomain X n) (𝟙 (wordDomain X n)))
    obtain ⟨l, hl⟩ := evaluate_factors_after_baseChange f N t ht n (𝟙 (wordDomain X n))
    have hl' : l ≫ N.inclusion.hom.hom = F.map w ≫ F.map B.inclusion.hom.hom :=
      hl.trans ((F.congr_map hw'.symm).trans (F.map_comp _ _))
    letI : IsSchemeTheoreticallyDominant (F.map w).left := baseChange_dominant w
    letI := N.isClosedImmersion
    obtain ⟨b, hb'⟩ := factor_through_dominant (F.map w) N.inclusion.hom.hom
      (F.map B.inclusion.hom.hom) ⟨l, hl'⟩
    obtain ⟨b', hfac⟩ := factor_group_through_subgroup N
      ((groupBaseChange k L).map B.inclusion) b hb'
    letI := hb
    letI : Mono N.inclusion := inclusion_mono N
    letI : IsSplitEpi N.inclusion := IsSplitEpi.mk' ⟨
      (groupBaseChange k L).map (inv B.inclusion) ≫ b', by
      rw [Category.assoc, hfac, ← Functor.map_comp, IsIso.inv_hom_id]
      exact (groupBaseChange k L).map_id G.val⟩
    exact isIso_of_mono_of_isSplitEpi _

private theorem simple_over_algClosed_extension [IsAlgClosed k] [IsAlgClosed L]
    {G : AffineAlgebraicGroup k} (hG : IsReductive G)
    (simple : ∀ N : ClosedSubgroup G.val, IsSmoothConnectedNormal N →
      IsTrivialSubgroup N ∨ IsIso N.inclusion)
    (N : ClosedSubgroup (baseChangedAlgebraicGroup L G).val)
    (hN : IsSmoothConnectedNormal N) : IsTrivialSubgroup N ∨ IsIso N.inclusion := by
  classical
  by_cases hnt : Nonempty (N.group ≅ Grp.trivial (SchemeOver L))
  · exact Or.inl hnt
  refine Or.inr ?_
  let F := groupBaseChange k L
  let Gext := baseChangedAlgebraicGroup L G
  have hGL := (Reductive.RadicalBaseChange.reductiveFieldExtension (K := L) G hG.1 hG.2.1).mpr hG
  obtain ⟨S, hS, hs⟩ := nontrivial_torus_in_normal (G := Gext) hGL N hN hnt
  let A := subgroupOfSubgroup N S
  obtain ⟨U, hU, j, hj⟩ := exists_maximal_torus_over Gext A hS
  obtain ⟨T, hT⟩ := maximalTorus_exists G
  let TL := extendSubgroup L T
  obtain ⟨g, e, he⟩ := MaximalToriConjugate.maximalToriConjugate Gext hGL.1
    (connected_of_geometricallyConnected hGL.2.1) U TL hU (extended_maximal_torus (L := L) hG T hT)
  let a := j ≫ e.hom
  have ha : a.hom.hom ≫ TL.inclusion.hom.hom =
      (toUnit S.group.X ≫ g) * (S.inclusion.hom.hom ≫ N.inclusion.hom.hom) *
        (toUnit S.group.X ≫ g)⁻¹ := by
    change j.hom.hom ≫ (e.hom ≫ TL.inclusion).hom.hom = _
    have hu : j.hom.hom ≫ toUnit U.group.X = toUnit S.group.X := toUnit_unique _ _
    have hg : j.hom.hom ≫ (toUnit U.group.X ≫ g) = toUnit S.group.X ≫ g :=
      (Category.assoc _ _ _).symm.trans (congrArg (· ≫ g) hu)
    rw [he, MonObj.comp_mul, MonObj.comp_mul, GrpObj.comp_inv, hg]
    have hj' := (Grp.forget (SchemeOver L)).congr_map hj
    change j.hom.hom ≫ U.inclusion.hom.hom =
      S.inclusion.hom.hom ≫ N.inclusion.hom.hom at hj'
    rw [hj']
  obtain ⟨z, hz⟩ := normalSubgroup_conjugate_sections hN.2.2 (toUnit S.group.X ≫ g)
    S.inclusion.hom.hom
  have hz' : z ≫ N.inclusion.hom.hom = (a ≫ TL.inclusion).hom.hom :=
    hz.trans ha.symm
  obtain ⟨b, hb⟩ := factor_group_through_subgroup N (a ≫ TL.inclusion) z hz'
  obtain ⟨r, ⟨q⟩⟩ := splitPresentation (splitTorus_of_torus (G := closedSubgroupAlgebraicGroup N) S hS)
  obtain ⟨m, ⟨p⟩⟩ := splitPresentation (splitTorus_of_torus T hT.1)
  let M := StandardLattice.{u} r
  let i := splitSchemeComparison (k := k) L M
  obtain ⟨d, hd⟩ := lift_split_hom p (q.hom ≫ a)
  have hfg : Group.FG M := by
    let e : Multiplicative ℤ ≃* IntegerCharacters.{u} := MulEquiv.ulift.symm
    have h : Group.FG IntegerCharacters.{u} :=
      Group.fg_of_surjective (f := e.toMonoidHom) e.surjective
    apply Group.fg_def.mpr
    simpa only [Subgroup.pi_top] using
      (Subgroup.FG.pi (P := fun (_ : Fin r) => (⊤ : Subgroup IntegerCharacters)) fun _ =>
        Group.fg_def.mp h)
  letI := hfg
  let J := diagonalGroup k M
  obtain ⟨eJ⟩ := LinearAlgebraicGroups.CharacterDescent.standardSplitTorus (k := k) r
  have hJ : IsSplitTorus J.val := ⟨r, ⟨eJ⟩⟩
  let d' : J.val ⟶ G.val := d ≫ T.inclusion
  have hd' : i.hom ≫ F.map d' = q.hom ≫ a ≫ TL.inclusion := by
    change i.hom ≫ F.map (d ≫ T.inclusion) = _
    rw [F.map_comp, ← Category.assoc, hd, Category.assoc]
    rfl
  have hnz : ¬ Nonempty (F.obj J.val ≅ Grp.trivial (SchemeOver L)) := by
    rintro ⟨v⟩
    exact hs ⟨q.symm ≪≫ i ≪≫ v⟩
  letI : Mono A.inclusion := inclusion_mono A
  letI : Mono j := mono_of_mono_fac hj
  letI : Mono TL.inclusion := inclusion_mono TL
  have hm : Mono (q.hom ≫ a ≫ TL.inclusion) := by
    dsimp only [a]
    infer_instance
  letI hm' : Mono (i.hom ≫ F.map d') := hd'.symm ▸ hm
  letI : Mono (F.map d') := by
    have heq : i.inv ≫ (i.hom ≫ F.map d') = F.map d' := i.inv_hom_id_assoc _
    exact heq ▸ (inferInstance : Mono (i.inv ≫ (i.hom ≫ F.map d')))
  apply normal_subgroup_full_of_extended_split_torus (L := L) (J := J) hG hJ simple d' N hN.2.2
    (i.inv ≫ q.hom ≫ b) ?_ hnz
  rw [Category.assoc, Category.assoc, hb, ← hd', Iso.inv_hom_id_assoc]

theorem absolutelyAlmostSimpleFieldExtension : AbsolutelyAlmostSimpleFieldExtension.{u} := by
  intro K F _ _ _ G hG
  let k := AlgebraicClosure K
  let L := AlgebraicClosure F
  let f : k →ₐ[K] L := IsAlgClosed.lift
  letI : Algebra k L := f.toRingHom.toAlgebra
  letI : IsScalarTower K k L := IsScalarTower.of_algebraMap_eq' (by
    ext a
    exact (f.commutes a).symm)
  let e : (groupBaseChange k L).obj (GeometricGroup G).val ≅
      (GeometricGroup (baseChangedAlgebraicGroup F G)).val :=
    ((groupBaseChangeTower (K := k) L).app G.val).symm ≪≫
      (groupBaseChangeTower (K := F) L).app G.val
  refine ⟨(Reductive.RadicalBaseChange.semisimpleFieldExtension (K := F) G hG.1.1 hG.1.2.1).mpr hG.1,
    ?_, ?_⟩
  · rintro ⟨q⟩
    apply hG.2.1
    exact (trivial_baseChange_iff (k := k) (K := L) (GeometricGroup G).val).mp ⟨e ≪≫ q⟩
  · intro N hN
    let N' := transportSubgroup e.symm N
    have hN' : IsSmoothConnectedNormal
        (G := baseChangedAlgebraicGroup L (GeometricGroup G)) N' :=
      ⟨hN.1, hN.2.1, transport_normal e.symm N hN.2.2⟩
    rcases simple_over_algClosed_extension (L := L)
      (reductive_geometricGroup G (reductive_of_semisimple G hG.1)) hG.2.2 N' hN' with h | h
    · exact Or.inl h
    · apply Or.inr
      letI : IsIso N'.inclusion := h
      have hcomp : IsIso (N'.inclusion ≫ e.hom) := inferInstance
      rwa [show N'.inclusion ≫ e.hom = N.inclusion from
        by change (N.inclusion ≫ e.inv) ≫ e.hom = _; simp] at hcomp

end AbsoluteSimplicity

private theorem noncentral_extend {K F : Type u} [Field K] [Field F] [Algebra K F]
    {G : GroupScheme K} {c : Cocharacter G} (hc : IsNoncentral c)
    {Z : ClosedSubgroup G} (hZ : RepresentsSubgroup Z (fun _ g ↦ Centralizes c g))
    (e : MultiplicativeGroup F ≅ (groupBaseChange K F).obj (MultiplicativeGroup K)) :
    IsNoncentral (e.hom ≫ (groupBaseChange K F).map c) := by
  let X := ((groupBaseChange K F).obj G).X
  refine ⟨X, 𝟙 X, ?_⟩
  intro H
  obtain ⟨hi, hz⟩ := centralizerSchemeBaseChange K F c Z hZ
  obtain ⟨p, hp⟩ := (hz X (𝟙 X)).mp ((centralizes_precomposeIso e _ _).mp H)
  letI := mono_over Z.inclusion.hom.hom Z.isClosedImmersion
  have hp' : p ≫ (baseChange K F).map Z.inclusion.hom.hom =
      (baseChange K F).map (𝟙 G.X) :=
    hp.trans ((baseChange K F).map_id G.X).symm
  obtain ⟨q, hq⟩ := factor_of_baseChange F (𝟙 G.X) Z.inclusion.hom.hom p hp'
  obtain ⟨Y, g, hg⟩ := hc
  apply hg
  exact (hZ Y g).mpr ⟨g ≫ q, by simp [hq]⟩

private theorem globalField_infinite {K : Type u} [Field K]
    (D : GlobalFieldData.{u, v} K) : Infinite K := by
  cases D with
  | number h =>
      letI := h
      infer_instance
  | function F parameter =>
      by_contra h
      letI : Finite K := not_infinite_iff_finite.mp h
      exact parameter.transcendental (Algebra.IsAlgebraic.isAlgebraic parameter.element)

private def completionPointEquiv {K : Type u} [Field K] {G : AffineAlgebraicGroup K}
    (D : GlobalFieldData.{u, v} K) (i : MatrixRealization G) (w : D.Place) :
    (𝟙_ (SchemeOver (D.Completion w)) ⟶ (baseChangedAlgebraicGroup (D.Completion w) G).val.X) ≃*
      LocalPoints D i w :=
  (testPointSections (baseChangedAlgebraicGroup (D.Completion w) G).val).symm.trans
    (baseChangePointGroupEquiv (D.Completion w) G.val
      (CommAlgCat.of (D.Completion w) (D.Completion w)))

private theorem completionPointEquiv_apply {K : Type u} [Field K] {G : AffineAlgebraicGroup K}
    (D : GlobalFieldData.{u, v} K) (i : MatrixRealization G) (w : D.Place)
    (p : 𝟙_ (SchemeOver (D.Completion w)) ⟶ (baseChangedAlgebraicGroup (D.Completion w) G).val.X) :
    completionPointEquiv D i w p = baseChangePoint K (D.Completion w) G.val.X
      (CommAlgCat.of (D.Completion w) (D.Completion w)) (toUnit _ ≫ p) := by
  change baseChangePoint K (D.Completion w) G.val.X _
    ((testPointSections (baseChangedAlgebraicGroup (D.Completion w) G).val).symm p) = _
  apply congrArg (baseChangePoint K (D.Completion w) G.val.X _)
  change _ ≫ p = toUnit _ ≫ p
  exact congrArg (· ≫ p) (toUnit_unique _ _)

private theorem completionPointEquiv_image {K : Type u} [Field K] {G : AffineAlgebraicGroup K}
    (D : GlobalFieldData.{u, v} K) (i : MatrixRealization G) (w : D.Place)
    (H : ClosedSubgroup G.val) (g : LocalPoints D i w) :
    (∃ p ∈ SubgroupSections (extendSubgroup (D.Completion w) H) (𝟙_ (SchemeOver (D.Completion w))),
      completionPointEquiv D i w p = g) ↔
    ∃ h : Points H.group.X (CommAlgCat.of K (D.Completion w)), h ≫ H.inclusion.hom.hom = g := by
  let F := D.Completion w
  let R := CommAlgCat.of F F
  let H' := extendSubgroup F H
  let e := baseChangePointGroupEquiv F H.group R
  have hnat (p : 𝟙_ (SchemeOver F) ⟶ H'.group.X) :
      completionPointEquiv D i w (p ≫ H'.inclusion.hom.hom) =
        e ((testPointSections H'.group).symm p) ≫ H.inclusion.hom.hom := by
    exact (baseChangePointsSchemeNaturality K F H.inclusion.hom.hom R
      ((testPointSections H'.group).symm p))
  constructor
  · rintro ⟨p, ⟨q, rfl⟩, rfl⟩
    exact ⟨_, (hnat q).symm⟩
  · rintro ⟨h, rfl⟩
    obtain ⟨q, rfl⟩ := ((testPointSections H'.group).symm.trans e).surjective h
    exact ⟨q ≫ H'.inclusion.hom.hom, ⟨q, rfl⟩, hnat q⟩

private theorem subgroupSections_eq {F : Type u} [Field F] {G : GroupScheme F}
    {A B : ClosedSubgroup G} (h : SameSubgroup A B) (X : SchemeOver F) :
    SubgroupSections A X = SubgroupSections B X := by
  have le {J L : ClosedSubgroup G} (hJL : Specs.SchemeDerivedGroup.IsSubgroupOf J L) :
      SubgroupSections J X ≤ SubgroupSections L X := by
    obtain ⟨f, hf⟩ := hJL
    rintro _ ⟨p, rfl⟩
    refine ⟨p ≫ f.hom.hom, ?_⟩
    change (p ≫ f.hom.hom) ≫ L.inclusion.hom.hom = p ≫ J.inclusion.hom.hom
    rw [Category.assoc]
    exact congrArg (p ≫ ·) ((Grp.forget (SchemeOver F)).congr_map hf)
  exact le_antisymm (le h.1) (le h.2)

private theorem closure_union_maps {M N : Type*} [Group M] [Group N]
    (φ : M →* N) (A B : Subgroup M) :
    Subgroup.closure (↑(A.map φ) ∪ ↑(B.map φ)) = (A ⊔ B).map φ := by
  rw [Subgroup.closure_union, Subgroup.closure_eq, Subgroup.closure_eq, Subgroup.map_sup]

private theorem generatedBySubgroups_eq_localPlus {K : Type u} [Field K]
    {G : AffineAlgebraicGroup K} (D : GlobalFieldData.{u, v} K) (i : MatrixRealization G)
    {c : Cocharacter G.val} (P : LimitDecomposition c)
    (Q : LimitDecomposition (oppositeCocharacter c)) (w : D.Place)
    {a : Cocharacter (baseChangedAlgebraicGroup (D.Completion w) G).val}
    (P' : LimitDecomposition a) (Q' : LimitDecomposition (oppositeCocharacter a))
    (hP : SameSubgroup P'.contracting (extendSubgroup (D.Completion w) P.contracting))
    (hQ : SameSubgroup Q'.contracting (extendSubgroup (D.Completion w) Q.contracting))
    (hgen : SubgroupSections P'.contracting (𝟙_ _) ⊔ SubgroupSections Q'.contracting (𝟙_ _) =
      unipotentGenerated (baseChangedAlgebraicGroup (D.Completion w) G)) :
    (generatedBySubgroups (fixedRadicals P Q) D i w : Set (LocalPoints D i w)) =
      localPlus D i w := by
  let φ := (completionPointEquiv D i w).toMonoidHom
  let F := D.Completion w
  let A := SubgroupSections (extendSubgroup F P.contracting) (𝟙_ (SchemeOver F))
  let B := SubgroupSections (extendSubgroup F Q.contracting) (𝟙_ (SchemeOver F))
  have hA : SubgroupSections P'.contracting (𝟙_ _) = A :=
    subgroupSections_eq hP _
  have hB : SubgroupSections Q'.contracting (𝟙_ _) = B :=
    subgroupSections_eq hQ _
  have hp0 : localPlus D i w =
      ↑((unipotentGenerated (baseChangedAlgebraicGroup F G)).map φ) := by
    apply Set.ext
    intro g
    change (∃ p ∈ unipotentGenerated (baseChangedAlgebraicGroup F G),
      baseChangePoint K F G.val.X (CommAlgCat.of F F) (toUnit _ ≫ p) = g) ↔
      g ∈ (unipotentGenerated (baseChangedAlgebraicGroup F G)).map φ
    constructor
    · rintro ⟨p, hp, rfl⟩
      exact Subgroup.mem_map.mpr ⟨p, hp, completionPointEquiv_apply D i w p⟩
    · intro hg
      obtain ⟨p, hp, he⟩ := Subgroup.mem_map.mp hg
      exact ⟨p, hp, (completionPointEquiv_apply D i w p).symm.trans he⟩
  have hAB : A ⊔ B = unipotentGenerated (baseChangedAlgebraicGroup F G) :=
    (congrArg₂ (· ⊔ ·) hA hB).symm.trans hgen
  have himage :
      {g : LocalPoints D i w | ∃ (j : ULift.{u} Bool)
        (h : Points (fixedRadicals P Q j).group.X (CommAlgCat.of K F)),
        h ≫ (fixedRadicals P Q j).inclusion.hom.hom = g} =
      ↑(A.map φ) ∪ ↑(B.map φ) := by
    ext g
    change (∃ (j : ULift.{u} Bool)
      (h : Points (fixedRadicals P Q j).group.X (CommAlgCat.of K F)),
      h ≫ (fixedRadicals P Q j).inclusion.hom.hom = g) ↔
      g ∈ A.map φ ∨ g ∈ B.map φ
    have hA' : g ∈ A.map φ ↔
        ∃ h : Points P.contracting.group.X (CommAlgCat.of K F),
          h ≫ P.contracting.inclusion.hom.hom = g :=
      Subgroup.mem_map.trans (completionPointEquiv_image D i w P.contracting g)
    have hB' : g ∈ B.map φ ↔
        ∃ h : Points Q.contracting.group.X (CommAlgCat.of K F),
          h ≫ Q.contracting.inclusion.hom.hom = g :=
      Subgroup.mem_map.trans (completionPointEquiv_image D i w Q.contracting g)
    constructor
    · rintro ⟨⟨j⟩, hj⟩
      cases j
      · exact Or.inl (hA'.mpr hj)
      · exact Or.inr (hB'.mpr hj)
    · rintro (h | h)
      · exact ⟨⟨false⟩, hA'.mp h⟩
      · exact ⟨⟨true⟩, hB'.mp h⟩
  have h := (congrArg (@Subgroup.closure (LocalPoints D i w) _) himage).trans
    (closure_union_maps φ A B)
  have hmaps := congrArg (fun C => Subgroup.map φ C) hAB
  exact (congrArg SetLike.coe (h.trans hmaps)).trans hp0.symm

theorem localGeneration : LocalGeneration.{u, v} := by
  intro K _ D G i hG c hc P Q w
  let F := D.Completion w
  let G' := baseChangedAlgebraicGroup F G
  obtain ⟨e, he⟩ := gm_baseChange K F
  let c' : Cocharacter G'.val := e.hom ≫ (groupBaseChange K F).map c
  have hc' := noncentral_extend hc P.centralizer_points e
  obtain ⟨P'⟩ := existsLimitDecomposition G' c'
  obtain ⟨Q'⟩ := existsLimitDecomposition G' (oppositeCocharacter c')
  obtain ⟨hP, hU, _⟩ := limits_subgroups_extend G P e he P'
  have hop : oppositeCocharacter c' = e.hom ≫ (groupBaseChange K F).map (oppositeCocharacter c) :=
    opposite_baseChange c e he
  obtain ⟨hQ, hV⟩ : SameSubgroup Q'.parabolic (extendSubgroup F Q.parabolic) ∧
      SameSubgroup Q'.contracting (extendSubgroup F Q.contracting) := by
    have aux (b : Cocharacter G'.val)
        (hb : b = e.hom ≫ (groupBaseChange K F).map (oppositeCocharacter c))
        (L : LimitDecomposition b) :
        SameSubgroup L.parabolic (extendSubgroup F Q.parabolic) ∧
        SameSubgroup L.contracting (extendSubgroup F Q.contracting) := by
      subst b
      obtain ⟨h₁, h₂, _⟩ := limits_subgroups_extend G Q e he L
      exact ⟨h₁, h₂⟩
    exact aux _ hop Q'
  have hG' := absolutelyAlmostSimpleFieldExtension (F := F) G hG
  have hR := reductive_of_semisimple G' hG'.1
  letI : Infinite K := globalField_infinite D
  letI : Infinite F := Infinite.of_injective (algebraMap K F) (algebraMap K F).injective
  have hgen := RelativeRayGeneration.twoRadicalsGenerate G' hG' c' hc' P' Q'
  exact ⟨e, he, hc', P', Q', (extendSubgroup F P.parabolic).isClosedImmersion,
    (extendSubgroup F Q.parabolic).isClosedImmersion,
    (extendSubgroup F P.contracting).isClosedImmersion, (extendSubgroup F Q.contracting).isClosedImmersion,
    hP, hQ, hU, hV, cocharacter_parabolic hR _ P', cocharacter_parabolic hR _ Q',
    Relative.SplitContractingRadical.contractingSubgroupIsRadical G' hR _ P',
    Relative.SplitContractingRadical.contractingSubgroupIsRadical G' hR _ Q',
    generatedBySubgroups_eq_localPlus D i P Q w P' Q' hU hV hgen⟩

theorem approximation : Approximation.{u, v} := by
  intro K _ D G i hG c hc P Q
  have hR := reductive_of_semisimple G hG.1
  let H := fixedRadicals P Q
  choose A hA e₀ using fun j : ULift.{u} Bool => groupPresentation (closedSubgroupAlgebraicGroup (H j))
  let e (j : ULift.{u} Bool) : specGroup (A j) ≅ (H j).group := (e₀ j).some
  have coords (j : ULift.{u} Bool) : ∃ n : ℕ, Nonempty (MvPolynomial (Fin n) K ≃ₐ[K] A j) := by
    obtain ⟨j⟩ := j
    cases j with
    | false =>
      obtain ⟨n, _, b, _, _⟩ :=
        Relative.SplitContractingRadical.contractingPolynomialCoordinates G hR c P (A ⟨false⟩) (e ⟨false⟩)
      exact ⟨n, ⟨b⟩⟩
    | true =>
      obtain ⟨n, _, b, _, _⟩ :=
        Relative.SplitContractingRadical.contractingPolynomialCoordinates G hR _ Q (A ⟨true⟩) (e ⟨true⟩)
      exact ⟨n, ⟨b⟩⟩
  choose n b using coords
  have hgen (w : D.Place) :
      (generatedBySubgroups H D i w : Set (LocalPoints D i w)) = localPlus D i w := by
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hg⟩ :=
      localGeneration D G i hG c hc P Q w
    exact hg.2
  refine ⟨cocharacter_parabolic hR _ P, cocharacter_parabolic hR _ Q,
    Relative.SplitContractingRadical.contractingSubgroupIsRadical G hR _ P,
    Relative.SplitContractingRadical.contractingSubgroupIsRadical G hR _ Q, ?_⟩
  intro S hS
  obtain ⟨hword, hdense⟩ := subgroupsWithPolynomialCoordinates D i S hS
    (n := n) H A e (fun j => (b j).some)
  refine ⟨fun x hx hg => hword x hx fun w => ?_, fun hd => hdense fun w => ?_⟩
  · change x w ∈ (generatedBySubgroups H D i w.1 : Set (LocalPoints D i w.1))
    rw [hgen]
    exact hg w
  · rw [hgen]
    exact hd w

end

end LinearAlgebraicGroups.Arithmetic.OppositeRadicals
