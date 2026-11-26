import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Arithmetic.LocalMixingSingletonRootSL2
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.TrialitarianRelativeRoots
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.LocalMixingRootMarkNormalization
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.LocalMixingMarkedMatrixDescent
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Relative.RelativeChambers
import Batteries.Tactic.OpenPrivate

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj TensorProduct Matrix

universe u

namespace LinearAlgebraicGroups.Arithmetic.LocalMixingSingletonRootSL2

open LinearAlgebraicGroups.Specs
open Specs.Arithmetic.LocalMixingSingletonRootSL2
open CharacterDescent (Character Cocharacter)
open CharacterPairing (absoluteRoots adjointWeightVectors characterValue pairing)
open AbstractPairing (Datum Root)
open DatumAndWeyl (Identification)
open Specs.GeometricRadicals
  (IsSplitReductive IsSplitTorus IsTorus baseChangedSubgroup IsReductive IsSemisimple)
open Specs.RankOneFlag (IsGeometricallyMaximal SameSubgroup)
open Specs.Relative.RelativeChambers (relativeRoots)
open Specs.Relative.MaximalSplitTori (IsMaximalSplitTorus)
open SchemeDerivedGroup (IsSubgroupOf)
open Specs.Unipotent (baseChangedAlgebraicGroup closedSubgroupAlgebraicGroup)
open Specs.QuasiSplitOrbitLevis (MultiplicativeComparison PreservesUnits)
open Specs.RootGroups (AdditiveLine HasScalarAction IsRootSubgroup rootPoint)
open Specs.AdjointRepresentation (GroupPoints)
open Specs.Arithmetic.TrialitarianFixedRootSL2 (RankOne)
open Specs.GeneralLinearStructure (SpecialMatrixPoints)
open Specs.Unipotent (Index)
open Specs.SimplyConnectedLattice (GeometricallySimplyConnected corootLatticeOf)
open CocharacterDynamics (LimitDecomposition oppositeCocharacter cocharacterPoint)

open private differential_injective map_weightVector splitTorus_baseChange pairing_inv
  connected_of_geometricallyConnected exists_regular_cocharacter
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.RootData.BorelsAndChambers
open private comp_conjugation conjugationIso from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Descent.FiniteFieldFlags
open private pushSubgroup from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.RootData.OrderedRootProducts
open private geometricallyMaximalOfIso from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.QuasiSplitOrbitLevis
open private extendSubgroup extend_subgroupOf subgroupOf_of_extend same_subgroup_of_same_sections
  centralizes_opposite_iff
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.RootData.RankOneFlag
open private isTorus_of_split from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.RootData.CharacterPairing
open private geometricallyMaximal_baseChange
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.QuasiSplitBorelPairBaseChange
open private conjugates_iff_iso from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Descent.FiniteFieldFlags
open private rootPoint_surjective rootPoint_hasLimit
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.RootData.OrderedRootProducts
open private rootPoint_comp normalizes_of_point_conjugation tangent_weight_of_scalarAction
  rootPoint_zero rootPoint_eps_reduces rootPoint_injective_of_mono dualTest characterValue_natural
  rootPoint_natural
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.RootData.RootGroups
open private scalarCharacter scalarCharacter_comparison scalarCharacterEquiv scalarRoot
  scalarRootEquiv scalarCocharacter_comparison scalarDatumAction scalarDatum_coweight
  scalarMorphism scalarMorphism_comp scalarMorphism_baseChange scalarMorphism_descends
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.QuasiSplitFixedWeyl
open private unitComparison_unique limitProperOfNegative
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.TrialitarianRelativeRoots
open private multiplicativeBaseChange multiplicativeBaseChange_unit
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Relative.RationalCocharacter
open private multiplicativeGroupAlgebra from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Reductive.NormalizerLatticeAction
open private cocharacterFactorsThroughMaximalSplit limitIsParabolic
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Relative.MaximalSplitTori
open private pairing_extended from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.RelativeRootIrreducibility
open private oppositeCocharacter_eq_inv from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Flag.BruhatOrbitParametrization
open private mono_over from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Affine.Stabilizers
open private subgroupInclusionFactors from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Reductive.CocharacterLimitSubgroups
open private splitBorelPair corootLattice_splitBorelPair
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Classification.SimplyConnectedLattice
open private reductive_of_semisimple from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Classification.CentralIsogenies
open private characterValue_extend from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Relative.RelativeChambers
open private mapPoints_injective from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Classification.RankOneRelations
open LinearAlgebraicGroups.WeilRestriction (extendScalars)

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
set_option linter.style.haveILetI false

variable {F : Type u} [Field F]

private theorem inclusion_square_symm {X Y T V : GroupScheme F}
    (f : X ≅ Y) (e : T ≅ V) (i : T ⟶ X) (j : V ⟶ Y)
    (h : e.hom ≫ j = i ≫ f.hom) :
    e.inv ≫ i = j ≫ f.inv := by
  calc
    e.inv ≫ i = e.inv ≫ (i ≫ f.hom) ≫ f.inv := by simp
    _ = j ≫ f.inv := by
      rw [← h, ← Category.assoc e.inv]
      exact congrArg (· ≫ f.inv) (e.inv_hom_id_assoc j)

private theorem root_of_isomorphism {X Y : GroupScheme F} (f : X ≅ Y)
    {S : ClosedSubgroup X} {T : ClosedSubgroup Y} (e : S.group ≅ T.group)
    (h : e.hom ≫ T.inclusion = S.inclusion ≫ f.hom)
    {a : Character T.group} (ha : e.hom ≫ a ∈ absoluteRoots S) :
    a ∈ absoluteRoots T := by
  obtain ⟨ha₁, v, hweight, hv⟩ := ha
  haveI : IsIso f.hom.hom.hom := (Grp.forget (SchemeOver F)).map_isIso f.hom
  refine ⟨fun h₁ => ha₁ ?_, mapPointKernel f.hom v, map_weightVector f.hom e h.symm hweight, ?_⟩
  · rw [h₁]
    exact Grp.hom_ext _ _ (MonObj.comp_one _)
  · intro hzero
    apply hv
    apply differential_injective f.hom
    exact hzero.trans (map_zero (mapPointKernel f.hom)).symm

private theorem absoluteRoots_iso {X Y : GroupScheme F} (f : X ≅ Y)
    {S : ClosedSubgroup X} {T : ClosedSubgroup Y} (e : S.group ≅ T.group)
    (h : e.hom ≫ T.inclusion = S.inclusion ≫ f.hom) (a : Character S.group) :
    e.inv ≫ a ∈ absoluteRoots T ↔ a ∈ absoluteRoots S := by
  constructor
  · exact root_of_isomorphism f.symm e.symm (inclusion_square_symm f e _ _ h)
  · intro ha
    apply root_of_isomorphism f e h
    simpa only [Iso.hom_inv_id_assoc] using ha

private theorem singleAbsoluteRoot_of_automorphism {G : AffineAlgebraicGroup F}
    (q : G.val ≅ G.val) {S S' : ClosedSubgroup G.val} (d : S.group ≅ S'.group)
    (hd : d.hom ≫ S'.inclusion = S.inclusion ≫ q.hom)
    {a : Character S.group} (ha : HasSingleAbsoluteRoot S a) :
    HasSingleAbsoluteRoot S' (d.inv ≫ a) := by
  obtain ⟨T, i, hT, hm, hi, K, _, _, _, _, hclosed, e, hG, hsplit, he, hunique⟩ := ha
  let T' := pushSubgroup q T
  have hm' := geometricallyMaximalOfIso q T T' (Iso.refl _) (Category.id_comp _) hm
  let i' : S'.group ⟶ T'.group := d.inv ≫ i
  have hi' : i' ≫ T'.inclusion = S'.inclusion := by
    change (d.inv ≫ i) ≫ (T.inclusion ≫ q.hom) = _
    simp only [Category.assoc, ← Category.assoc i T.inclusion, hi]
    rw [← hd, Iso.inv_hom_id_assoc]
  let E := groupBaseChange F K
  let hclosed' := baseChangeClosedSubgroup F K T'.inclusion T'.isClosedImmersion
  refine ⟨T', i', hT, hm', hi', K, inferInstance, inferInstance, inferInstance, inferInstance,
    hclosed', e, hG, hsplit, he, ?_⟩
  have hroot (b : Character (E.obj T.group)) :
      b ∈ absoluteRoots (baseChangedSubgroup K T' hclosed') ↔
        b ∈ absoluteRoots (baseChangedSubgroup K T hclosed) := by
    have hsq : (Iso.refl (E.obj T.group)).hom ≫ (E.map T'.inclusion) =
        E.map T.inclusion ≫ (E.mapIso q).hom := by
      change 𝟙 _ ≫ E.map (T.inclusion ≫ q.hom) = E.map T.inclusion ≫ E.map q.hom
      rw [Category.id_comp, E.map_comp]
    have hr := absoluteRoots_iso (E.mapIso q) (S := baseChangedSubgroup K T hclosed)
      (T := baseChangedSubgroup K T' hclosed') (Iso.refl _) hsq b
    change _ ≫ b ∈ absoluteRoots (baseChangedSubgroup K T' hclosed') ↔ _ at hr
    change (𝟙 (E.obj T.group) ≫ b) ∈ _ ↔ _ at hr
    rwa [Category.id_comp] at hr
  have hrestriction (b : Character (E.obj T.group)) :
      E.map i' ≫ b = E.map (d.inv ≫ a) ≫ e.inv ↔ E.map i ≫ b = E.map a ≫ e.inv := by
    change E.map (d.inv ≫ i) ≫ b = E.map (d.inv ≫ a) ≫ e.inv ↔ _
    simp only [E.map_comp, Category.assoc]
    exact cancel_epi (E.map d.inv)
  obtain ⟨b, ⟨hb, hres⟩, huniq⟩ := hunique
  exact ⟨b, ⟨(hroot b).mpr hb, (hrestriction b).mpr hres⟩,
    fun c hc => huniq c ⟨(hroot c).mp hc.1, (hrestriction c).mp hc.2⟩⟩

theorem conjugationInvariance : ConjugationInvariance.{u} := by
  intro F _ _ _ _ G _ _ S S' _ _ g e he a
  let q := conjugationIso g
  have h : e.hom ≫ S'.inclusion = S.inclusion ≫ q.hom := by
    apply Grp.hom_ext
    exact he.trans (comp_conjugation g S.inclusion.hom.hom).symm
  refine ⟨(absoluteRoots_iso q e h a.val).mpr a.property, ?_⟩
  constructor
  · exact singleAbsoluteRoot_of_automorphism q e h
  · intro ha
    have hh := singleAbsoluteRoot_of_automorphism q.symm e.symm
      (inclusion_square_symm q e _ _ h) ha
    change HasSingleAbsoluteRoot S (e.hom ≫ e.inv ≫ a.val) at hh
    rwa [Iso.hom_inv_id_assoc] at hh

/- An isomorphism over the ground field preserves the structure morphism. -/
private theorem smooth_additiveLine (A : AdditiveLine F) : Smooth A.group.X.hom := by
  change Smooth (Spec.map (CommRingCat.ofHom (algebraMap F (Polynomial F))))
  rw [HasRingHomProperty.Spec_iff (P := @Smooth)]
  change (algebraMap F (Polynomial F)).Smooth
  exact RingHom.smooth_algebraMap.mpr ⟨inferInstance, inferInstance⟩

private theorem isRootSubgroup_of_scalarAction {X : GroupScheme F} (S U : ClosedSubgroup X)
    (a : Character S.group) (A : AdditiveLine F) (x : A.group ≅ U.group)
    (hx : HasScalarAction S a (x.hom ≫ U.inclusion)) : IsRootSubgroup S U a := by
  have hleft : IsIso x.hom.hom.hom.left :=
    ((Grp.forget (SchemeOver F)) ⋙ Over.forget _).map_isIso x.hom
  refine ⟨?_, ⟨A.operations, A.comultiplication, A.counit, A.antipode, ⟨x.symm⟩⟩, ?_,
    tangent_weight_of_scalarAction S U a A x hx⟩
  · exact (MorphismProperty.cancel_left_of_respectsIso @Smooth x.hom.hom.hom.left _).mp
      ((Over.w x.hom.hom.hom).symm ▸ smooth_additiveLine A)
  · apply normalizes_of_point_conjugation S U
    intro R t p
    obtain ⟨b, rfl⟩ := rootPoint_surjective x R p
    refine ⟨rootPoint x.hom R (characterValue a R t * b), ?_⟩
    rw [← rootPoint_comp, ← rootPoint_comp]
    exact (hx R t b).symm

private theorem maximalSplit_of_geometricallyMaximal {X : GroupScheme F}
    (T : ClosedSubgroup X) (hT : IsSplitTorus T.group)
    (hm : IsGeometricallyMaximal T) : IsMaximalSplitTorus T := by
  refine ⟨hT, ?_⟩
  intro S hs h
  obtain ⟨hc, hm⟩ := hm
  let K := AlgebraicClosure F
  have hr : IsSubgroupOf (extendSubgroup K S) (extendSubgroup K T) :=
    hm.2 (extendSubgroup K S) (isTorus_of_split (splitTorus_baseChange hs))
      (extend_subgroupOf h)
  exact subgroupOf_of_extend hr

private theorem geometricallyMaximal_of_maximalSplit {G : AffineAlgebraicGroup F}
    (hsplit : IsSplitReductive G) (S : ClosedSubgroup G.val) (hs : IsMaximalSplitTorus S) :
    IsGeometricallyMaximal S := by
  obtain ⟨hred, T, ht, hm⟩ := hsplit
  obtain ⟨g, hg⟩ := Relative.MaximalSplitTori.maximalSplitToriConjugate G hred T S
    (maximalSplit_of_geometricallyMaximal T ht hm) hs
  obtain ⟨e, he⟩ := (conjugates_iff_iso g T S).mp hg
  exact geometricallyMaximalOfIso (conjugationIso g) T S e he hm

private theorem singleAbsoluteRoot_of_split {G : AffineAlgebraicGroup F}
    (S : ClosedSubgroup G.val) (hred : IsReductive G) (hs : IsSplitTorus S.group)
    (hm : IsGeometricallyMaximal S) (a : relativeRoots S) : HasSingleAbsoluteRoot S a.val := by
  let E := groupBaseChange F F
  let S' := extendSubgroup F S
  have hs' : IsSplitTorus S'.group := splitTorus_baseChange hs
  have hr : IsReductive (baseChangedAlgebraicGroup F G) :=
    (Reductive.RadicalBaseChange.reductiveFieldExtension G hred.1 hred.2.1).mpr hred
  have hm' : IsGeometricallyMaximal S' :=
    geometricallyMaximal_baseChange G hred S (isTorus_of_split hs) hm hs'
  obtain ⟨e, he, _, hset⟩ :=
    Relative.RelativeChambers.relativeRootsByRestriction G S S (𝟙 _) (Category.id_comp _)
      hs S'.isClosedImmersion hs'
  let b : Character S'.group := E.map a.val ≫ e.inv
  have hb : b ∈ (fun a : Character S.group => E.map a ≫ e.inv) '' relativeRoots S :=
    ⟨a.val, a.property, rfl⟩
  rw [hset] at hb
  obtain ⟨c, hc, hcb⟩ := hb.1
  have hid (c : Character S'.group) : E.map (𝟙 S.group) ≫ c = c := by
    rw [E.map_id, Category.id_comp]
  change E.map (𝟙 S.group) ≫ c = b at hcb
  rw [hid] at hcb
  refine ⟨S, 𝟙 _, isTorus_of_split hs, hm, Category.id_comp _, F, inferInstance, inferInstance,
    inferInstance, inferInstance, S'.isClosedImmersion, e, ⟨hr, S', hs', hm'⟩, hs', he, ?_⟩
  refine ⟨b, ⟨hcb ▸ hc, hid b⟩, ?_⟩
  rintro c ⟨_, h⟩
  exact (hid c).symm.trans h

section GaloisDescent

variable {K : Type u} [Field K] [Algebra F K] {G : AffineAlgebraicGroup F}
variable {S T : ClosedSubgroup G.val}

/-- The restriction of a Galois translate equals the same base-changed
character, so singleton fibres are fixed pointwise. -/
private theorem singletonRoot_galoisFixed
    (i : S.group ⟶ T.group)
    (hT : IsClosedImmersion ((groupBaseChange F K).map T.inclusion).hom.hom.left)
    (e : MultiplicativeComparison F K) (he : PreservesUnits e)
    (a : Character S.group) (b : Character ((groupBaseChange F K).obj T.group))
    (hb : b ∈ absoluteRoots (baseChangedSubgroup K T hT))
    (hres : (groupBaseChange F K).map i ≫ b = (groupBaseChange F K).map a ≫ e.inv)
    (huniq : ∀ c ∈ absoluteRoots (baseChangedSubgroup K T hT),
      (groupBaseChange F K).map i ≫ c = (groupBaseChange F K).map a ≫ e.inv → c = b)
    (σ : Gal(K/F)) : scalarCharacter σ b = b := by
  let E := groupBaseChange F K
  let t := multiplicativeBaseChange F K
  have hte : e = t := unitComparison_unique he (multiplicativeBaseChange_unit K)
  subst e
  have h : E.map i ≫ (b ≫ t.hom) = E.map a := by
    rw [← Category.assoc, hres, Category.assoc, t.inv_hom_id, Category.comp_id]
  apply huniq _ (scalarRoot T hT σ b hb)
  apply (cancel_mono t.hom).mp
  calc
    (E.map i ≫ scalarCharacter σ b) ≫ t.hom =
        E.map i ≫ scalarMorphism σ (b ≫ t.hom) := by
      rw [Category.assoc]
      exact congrArg (E.map i ≫ ·) (scalarCharacter_comparison σ b)
    _ = scalarMorphism σ (E.map i ≫ (b ≫ t.hom)) := by
      rw [scalarMorphism_comp, scalarMorphism_baseChange]
    _ = E.map a := by rw [h, scalarMorphism_baseChange]
    _ = (E.map a ≫ t.inv) ≫ t.hom := by simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]

private theorem singletonCoroot_descends [IsGalois F K]
    (i : S.group ⟶ T.group) (hi : i ≫ T.inclusion = S.inclusion)
    (hS : IsMaximalSplitTorus S) (hTtorus : IsTorus T.group)
    (hT : IsClosedImmersion ((groupBaseChange F K).map T.inclusion).hom.hom.left)
    (hTk : IsSplitTorus ((groupBaseChange F K).obj T.group))
    [IsCommMonObj (baseChangedSubgroup K T hT).group.X]
    (D : Datum (G := baseChangedAlgebraicGroup K G) (baseChangedSubgroup K T hT))
    (W : Identification D) (a : Character S.group)
    (e : MultiplicativeComparison F K) (he : PreservesUnits e)
    (b : Root (G := baseChangedAlgebraicGroup K G) (baseChangedSubgroup K T hT))
    (hres : (groupBaseChange F K).map i ≫ b.val = (groupBaseChange F K).map a ≫ e.inv)
    (hfix : ∀ σ : Gal(K/F), scalarCharacter σ b.val = b.val) :
    ∃ c : Cocharacter S.group,
      Additive.ofMul (e.hom ≫ (groupBaseChange F K).map (c ≫ i)) = D.rootDatum.coroot b ∧
      pairing S.group a c = 2 := by
  let E := groupBaseChange F K
  let t := multiplicativeBaseChange F K
  have hte : e = t := unitComparison_unique he (multiplicativeBaseChange_unit K)
  subst e
  let y : Cocharacter (E.obj T.group) := (D.rootDatum.coroot b).toMul
  have hfixed (σ : Gal(K/F)) : scalarMorphism σ (t.inv ≫ y) = t.inv ≫ y := by
    have hi' : scalarRootEquiv (T := T) (hT := hT) σ b = b := Subtype.ext (hfix σ)
    let ρ := scalarDatumAction W hTk σ
    have hρ : ρ.indexEquiv b = b := hi'
    have hρ' : ρ.indexEquiv.symm b = b :=
      ρ.indexEquiv.symm_apply_eq.mpr hρ.symm
    have hcor : ρ.coweightEquiv (D.rootDatum.coroot b) = D.rootDatum.coroot b := by
      change ρ.coweightMap (D.rootDatum.coroot b) = _
      rw [RootPairing.Hom.coroot_coweightMap_apply, hρ']
    have hcor' : ρ.coweightEquiv.symm (D.rootDatum.coroot b) = D.rootDatum.coroot b :=
      ρ.coweightEquiv.symm_apply_eq.mpr hcor.symm
    rw [← scalarCocharacter_comparison]
    congr 1
    exact (congrArg Additive.toMul
      ((scalarDatum_coweight W hTk σ y).symm.trans hcor'))
  obtain ⟨cT, hcT⟩ := scalarMorphism_descends (multiplicativeGroupAlgebra F)
    (closedSubgroupAlgebraicGroup T) (t.inv ≫ y) hfixed
  obtain ⟨c, hc⟩ := cocharacterFactorsThroughMaximalSplit G S T hS hTtorus i hi cT
  have hcy : t.hom ≫ E.map (c ≫ i) = y := by rw [hc, hcT, Iso.hom_inv_id_assoc]
  refine ⟨c, congrArg Additive.ofMul hcy, ?_⟩
  have hp := pairing_extended K t he i a b.val hres c
  rw [← E.map_comp, hcy] at hp
  refine hp.symm.trans ?_
  exact (D.pairing_eq b.val y).symm.trans (by
    change D.rootDatum.toLinearMap (Additive.ofMul b.val) (D.rootDatum.coroot b) = 2
    rw [← D.root_eq b]
    exact D.rootDatum.coroot_root_two b)

private theorem baseChangedCoroot_isPrimitive [Algebra.IsAlgebraic F K]
    (hG : IsSemisimple G) (hsc : GeometricallySimplyConnected G)
    (hT : IsClosedImmersion ((groupBaseChange F K).map T.inclusion).hom.hom.left)
    (hTk : IsSplitTorus ((groupBaseChange F K).obj T.group))
    (hm : IsGeometricallyMaximal (baseChangedSubgroup K T hT))
    [IsCommMonObj (baseChangedSubgroup K T hT).group.X]
    (D : Datum (G := baseChangedAlgebraicGroup K G) (baseChangedSubgroup K T hT))
    (b : Root (G := baseChangedAlgebraicGroup K G) (baseChangedSubgroup K T hT)) :
    ∃ f : Additive (Cocharacter (baseChangedSubgroup K T hT).group) →ₗ[ℤ] ℤ,
      f (D.rootDatum.coroot b) = 1 := by
  let GK := baseChangedAlgebraicGroup K G
  let TK := baseChangedSubgroup K T hT
  have hss : IsSemisimple GK :=
    (Reductive.RadicalBaseChange.semisimpleFieldExtension G hG.1 hG.2.1).mpr hG
  have hr := reductive_of_semisimple GK hss
  let P := splitBorelPair GK hr TK hTk hm
  have hspan := QuasiSplitPinnedPairModel.corootLatticeAfterSplitting G hG hsc P
    (Classification.Pinning.attachedDatum P) ⟨Iso.refl _⟩
  have hspan' : corootLatticeOf D = ⊤ :=
    (corootLattice_splitBorelPair GK hr TK hTk hm D).symm.trans hspan
  obtain ⟨s, hs⟩ := exists_regular_cocharacter GK TK hTk
  letI := D.finiteRoots
  letI := D.freeCharacters
  letI := D.finiteCharacters
  letI := D.reduced
  have hregular (r : Root (G := baseChangedAlgebraicGroup K G) (baseChangedSubgroup K T hT)) :
      SimpleRoots.evaluate D s (D.rootDatum.root r) ≠ 0 := by
    change D.rootDatum.toLinearMap (D.rootDatum.root r) (Additive.ofMul s) ≠ 0
    rw [D.root_eq, D.pairing_eq]
    exact hs r
  obtain ⟨B, _⟩ := RootData.SimpleRoots.baseFor D.rootDatum (SimpleRoots.evaluate D s) hregular
  exact TrialitarianRelativeRoots.corootPrimitive D.rootDatum B hspan' b

private theorem invariantCharacter_descends [IsGalois F K] (T : ClosedSubgroup G.val)
    (e : MultiplicativeComparison F K) (he : PreservesUnits e)
    (b : Character ((groupBaseChange F K).obj T.group))
    (hb : ∀ σ : Gal(K/F), scalarCharacter σ b = b) :
    ∃ β : Character T.group, (groupBaseChange F K).map β ≫ e.inv = b := by
  let E := groupBaseChange F K
  let t := multiplicativeBaseChange F K
  have hte : e = t := unitComparison_unique he (multiplicativeBaseChange_unit K)
  subst e
  have h (σ : Gal(K/F)) : scalarMorphism σ (b ≫ t.hom) = b ≫ t.hom :=
    (scalarCharacter_comparison σ b).symm.trans (congrArg (· ≫ t.hom) (hb σ))
  obtain ⟨β, hβ⟩ := scalarMorphism_descends (closedSubgroupAlgebraicGroup T)
    (multiplicativeGroupAlgebra F) (b ≫ t.hom) h
  refine ⟨β, ?_⟩
  change E.map β ≫ t.inv = b
  rw [hβ, Category.assoc, t.hom_inv_id, Category.comp_id]

private theorem singletonCoroot_data [FiniteDimensional F K] [IsGalois F K]
    (hG : IsSemisimple G) (hsc : GeometricallySimplyConnected G) (hS : IsMaximalSplitTorus S)
    (hTtorus : IsTorus T.group) (hTm : IsGeometricallyMaximal T)
    (i : S.group ⟶ T.group) (hi : i ≫ T.inclusion = S.inclusion)
    (hT : IsClosedImmersion ((groupBaseChange F K).map T.inclusion).hom.hom.left)
    (hs : IsSplitReductive (baseChangedAlgebraicGroup K G))
    (hTk : IsSplitTorus ((groupBaseChange F K).obj T.group))
    (e : MultiplicativeComparison F K) (he : PreservesUnits e) (a : Character S.group)
    (h : ∃! b : Character ((groupBaseChange F K).obj T.group),
      b ∈ absoluteRoots (baseChangedSubgroup K T hT) ∧
        (groupBaseChange F K).map i ≫ b = (groupBaseChange F K).map a ≫ e.inv) :
    ∃ hcomm : IsCommMonObj (baseChangedSubgroup K T hT).group.X,
      letI := hcomm
      ∃ (D : Datum (G := baseChangedAlgebraicGroup K G) (baseChangedSubgroup K T hT))
        (b : Root (G := baseChangedAlgebraicGroup K G) (baseChangedSubgroup K T hT))
        (c : Cocharacter S.group),
        (groupBaseChange F K).map i ≫ b.val = (groupBaseChange F K).map a ≫ e.inv ∧
        (∀ σ : Gal(K/F), scalarCharacter σ b.val = b.val ∧
          scalarCharacter σ b.val⁻¹ = b.val⁻¹) ∧
        Additive.ofMul (e.hom ≫ (groupBaseChange F K).map (c ≫ i)) = D.rootDatum.coroot b ∧
        pairing S.group a c = 2 ∧
        ∃ f : Additive (Cocharacter (baseChangedSubgroup K T hT).group) →ₗ[ℤ] ℤ,
          f (D.rootDatum.coroot b) = 1 := by
  obtain ⟨b, ⟨hb, hres⟩, huniq⟩ := h
  have hfix (σ : Gal(K/F)) : scalarCharacter σ b = b :=
    singletonRoot_galoisFixed i hT e he a b hb hres (fun z hz hza => huniq z ⟨hz, hza⟩) σ
  let GK := baseChangedAlgebraicGroup K G
  let TK := baseChangedSubgroup K T hT
  have hm : IsGeometricallyMaximal TK :=
    geometricallyMaximal_baseChange G (reductive_of_semisimple G hG) T hTtorus hTm hTk
  obtain ⟨hcomm, hdatum⟩ := RootData.DatumAndWeyl.datumAndWeyl GK hs.1 TK hTk hm
  letI : IsCommMonObj (baseChangedSubgroup K T hT).group.X := hcomm
  obtain ⟨D, ⟨W⟩⟩ := hdatum
  let r : Root (G := baseChangedAlgebraicGroup K G) (baseChangedSubgroup K T hT) := ⟨b, hb⟩
  obtain ⟨c, hc, hp⟩ := singletonCoroot_descends i hi hS hTtorus hT hTk D W a e he r hres hfix
  refine ⟨hcomm, D, r, c, hres, fun σ => ⟨hfix σ, ?_⟩, hc, hp,
    baseChangedCoroot_isPrimitive hG hsc hT hTk hm D r⟩
  exact (map_inv (scalarCharacterEquiv σ T.group) b).trans (congrArg Inv.inv (hfix σ))

end GaloisDescent

private theorem scalarAction_of_baseChange {K : Type u} [Field K] [Algebra F K]
    {G : AffineAlgebraicGroup F} {S T : ClosedSubgroup G.val}
    {i : S.group ⟶ T.group} (hi : i ≫ T.inclusion = S.inclusion)
    (hT : IsClosedImmersion ((groupBaseChange F K).map T.inclusion).hom.hom.left)
    (e : MultiplicativeComparison F K) (he : PreservesUnits e)
    (a : Character S.group) (b : Character ((groupBaseChange F K).obj T.group))
    (hres : (groupBaseChange F K).map i ≫ b = (groupBaseChange F K).map a ≫ e.inv)
    {A : AdditiveLine F} {B : AdditiveLine K}
    (x : A.group ⟶ G.val) (y : B.group ⟶ (groupBaseChange F K).obj G.val)
    (hy : HasScalarAction (baseChangedSubgroup K T hT) b y)
    (hcoord : ∀ (R : TestAlgebra K) (z : R),
      baseChangePoint F K G.val.X R (rootPoint y R z) =
        rootPoint x ((restrictTestAlgebra F K).obj R) z) :
    HasScalarAction S a x := by
  intro R s z
  let E := groupBaseChange F K
  let R' : TestAlgebra K := (extendScalars F K).obj R
  let R₀ := (restrictTestAlgebra F K).obj R'
  let j : R →+* (R ⊗[F] K) :=
    (Algebra.TensorProduct.includeLeft (R := F) (S := F) (A := R) (B := K)).toRingHom
  letI : Algebra F R₀ := R₀.algebra
  let f₀ : R →ₐ[F] R₀ :=
    { toRingHom := j
      commutes' a := by
        change (algebraMap F R a) ⊗ₜ[F] (1 : K) =
          (1 : R) ⊗ₜ[F] (algebraMap F K a)
        simpa only [Algebra.algebraMap_eq_smul_one] using
          (TensorProduct.smul_tmul (R := F) a (1 : R) (1 : K)) }
  let f : R ⟶ R₀ := ConcreteCategory.ofHom (C := CommAlgCat F) f₀
  have hf : Function.Injective f.hom := by
    change Function.Injective j
    exact Algebra.TensorProduct.includeLeft_injective (S := F) (algebraMap F K).injective
  let s' := (baseChangePointGroupEquiv K S.group R').symm (mapPoints f s)
  let t' : GroupPoints (E.obj T.group) R' := s' ≫ (E.map i).hom.hom
  let g' : GroupPoints (E.obj G.val) R' := t' ≫ (E.map T.inclusion).hom.hom
  have hs : baseChangePoint F K S.group.X R' s' = mapPoints f s :=
    (baseChangePointGroupEquiv K S.group R').apply_symm_apply (mapPoints f s)
  have hval : characterValue b R' t' = f.hom (characterValue a R s) := by
    have h := characterValue_extend a e he R' s'
    rw [← hres, hs, characterValue_natural] at h
    exact h
  have hg : baseChangePointGroupEquiv K G.val R' g' =
      mapPoints f (s ≫ S.inclusion.hom.hom) := by
    have h : (E.map i).hom.hom ≫ (E.map T.inclusion).hom.hom = (E.map S.inclusion).hom.hom :=
      (Grp.forget (SchemeOver K)).congr_map ((E.map_comp i T.inclusion).symm.trans (E.congr_map hi))
    change baseChangePoint F K G.val.X R' ((s' ≫ (E.map i).hom.hom) ≫
      (E.map T.inclusion).hom.hom) = _
    rw [Category.assoc, h]
    calc
      _ = baseChangePoint F K S.group.X R' s' ≫ S.inclusion.hom.hom :=
        baseChangePointsSchemeNaturality F K S.inclusion.hom.hom R' s'
      _ = _ := by
        rw [hs]
        exact Category.assoc _ _ _
  let g : GroupPoints G.val R := s ≫ S.inclusion.hom.hom
  have h := hy R' t' (f.hom z)
  change g' * rootPoint y R' (f.hom z) * g'⁻¹ =
    rootPoint y R' (characterValue b R' t' * f.hom z) at h
  have h' := congrArg (baseChangePointGroupEquiv K G.val R') h
  rw [map_mul, map_mul, map_inv, hg] at h'
  change mapPoints f g * baseChangePoint F K G.val.X R' (rootPoint y R' (f.hom z)) *
    (mapPoints f g)⁻¹ = baseChangePoint F K G.val.X R'
      (rootPoint y R' (characterValue b R' t' * f.hom z)) at h'
  rw [hcoord, hcoord, hval, ← map_mul, ← rootPoint_natural, ← rootPoint_natural] at h'
  apply mapPoints_injective G.property.1 f hf
  change (((groupPointsFunctor F).obj G.val).map f).hom
      (g * rootPoint x R z * g⁻¹) =
    (((groupPointsFunctor F).obj G.val).map f).hom
      (rootPoint x R (characterValue a R s * z))
  rw [map_mul, map_mul, map_inv]
  exact h'

private theorem root_of_scalarAction {X : GroupScheme F} (S U : ClosedSubgroup X)
    (a : Character S.group) (A : AdditiveLine F) (e : A.group ≅ U.group)
    (ha : a ≠ 1) (h : HasScalarAction S a (e.hom ≫ U.inclusion)) : a ∈ absoluteRoots S := by
  let v : Lie F U.group :=
    ⟨rootPoint e.hom (dualTest F) (DualNumber.eps : DualNumber F), rootPoint_eps_reduces e.hom⟩
  let f := e.hom ≫ U.inclusion
  have hm : Mono U.inclusion.hom.hom := mono_over _ U.isClosedImmersion
  have hm' : Mono f.hom.hom :=
    inferInstanceAs (Mono (e.hom.hom.hom ≫ U.inclusion.hom.hom))
  refine ⟨ha, mapPointKernel U.inclusion v, (tangent_weight_of_scalarAction S U a A e h)
    ⟨v, rfl⟩, ?_⟩
  intro hzero
  have heq := congrArg (fun w : Lie F X => w.toMul.val) hzero
  change rootPoint e.hom (dualTest F) _ ≫ U.inclusion.hom.hom = 1 at heq
  rw [← rootPoint_comp, ← rootPoint_zero f (dualTest F)] at heq
  have heps := rootPoint_injective_of_mono f (dualTest F) heq
  have h10 : (1 : F) = 0 := congrArg TrivSqZeroExt.snd heps
  exact one_ne_zero h10

private theorem scalarAction_subgroupOf_contracting {G : AffineAlgebraicGroup F}
    (S U : ClosedSubgroup G.val) (a : Character S.group) (A : AdditiveLine F)
    (x : A.group ≅ U.group) (h : HasScalarAction S a (x.hom ≫ U.inclusion))
    (c : Cocharacter S.group) (hc : 0 < pairing S.group a c)
    (C : LimitDecomposition (c ≫ S.inclusion)) :
    IsSubgroupOf U C.contracting := by
  apply subgroupInclusionFactors (closedSubgroupAlgebraicGroup U).property.1
  intro R p
  obtain ⟨b, rfl⟩ := rootPoint_surjective x R p
  apply (C.contracting_points R _).mp
  change CocharacterDynamics.HasLimit (c ≫ S.inclusion)
    (rootPoint x.hom R b ≫ U.inclusion.hom.hom) 1
  rw [← rootPoint_comp]
  exact rootPoint_hasLimit h c hc R b

theorem rankOne_oppositeRadicals {G : AffineAlgebraicGroup F} (hG : IsReductive G)
    {S : ClosedSubgroup G.val} (hS : IsSplitTorus S.group) (L : RankOne S)
    (a : relativeRoots S) (hp : pairing S.group a.val L.cochar = 2)
    (hpos : HasScalarAction S a.val (L.upper.hom ≫ L.positive.inclusion))
    (hneg : HasScalarAction S a.val⁻¹ (L.lower.hom ≫ L.negative.inclusion)) :
    Specs.Arithmetic.TrialitarianRelativeRoots.RankOne.HasOppositeRadicals L := by
  have ha : a.val ≠ 1 := a.property.1
  have hn : a.val⁻¹ ≠ 1 := by
    intro h
    apply ha
    calc
      a.val = (a.val⁻¹)⁻¹ := (inv_inv _).symm
      _ = 1 := by rw [h, inv_one]
  let b : Root S := ⟨a.val⁻¹, root_of_scalarAction S L.negative a.val⁻¹ L.additive L.lower hn hneg⟩
  let c := L.cochar
  let d := c ≫ S.inclusion
  have hη : oppositeCocharacter d = oppositeCocharacter c ≫ S.inclusion :=
    (Category.assoc _ _ _).symm
  have hopp (χ : Character S.group) :
      pairing S.group χ (oppositeCocharacter c) = -pairing S.group χ c := by
    obtain ⟨hComm, _, _, _, _, P, _, hP⟩ := RootData.CharacterPairing.perfectCharacterPairing S.group hS
    letI := hComm
    rw [oppositeCocharacter_eq_inv, ← hP, ← hP]
    exact map_neg (P (Additive.ofMul χ)) (Additive.ofMul c)
  have hminus : pairing S.group b.val c = -2 := by
    change pairing S.group a.val⁻¹ c = -2
    rw [pairing_inv S.group hS, hp]
  letI := hG.1
  letI : ConnectedSpace G.val.X.left := connected_of_geometricallyConnected hG.2.1
  obtain ⟨C, E, _, _, _, _, _, _, _, _, _, _, hcell, _, _⟩ := CocharacterDynamics.cocharacterDynamics G d
  let E' : LimitDecomposition (oppositeCocharacter c ≫ S.inclusion) := hη ▸ E
  have hP : ¬ IsIso E'.parabolic.inclusion :=
    limitProperOfNegative G S (oppositeCocharacter c) E' a (by rw [hopp, hp]; decide)
  have hU := scalarAction_subgroupOf_contracting S L.positive _ L.additive L.upper hpos c
    (by rw [hp]; decide) C
  have hV := scalarAction_subgroupOf_contracting S L.negative b.val L.additive L.lower hneg
    (oppositeCocharacter c) (by rw [hopp, hminus]; decide) E'
  have heP : E'.parabolic = E.parabolic := by
    unfold E'
    generalize hη = he
    cases he
    rfl
  have heU : E'.contracting = E.contracting := by
    unfold E'
    generalize hη = he
    cases he
    rfl
  exact ⟨C, E, limitIsParabolic G hG _ C, limitIsParabolic G hG _ E,
    limitProperOfNegative G S c C b (by rw [hminus]; decide), heP ▸ hP,
    same_subgroup_of_same_sections (H := G) C.centralizer_points
      (fun Y y => (centralizes_opposite_iff d y).symm.trans (E.centralizer_points Y y)),
    hcell, Relative.SplitContractingRadical.contractingSubgroupIsRadical G hG _ C,
    Relative.SplitContractingRadical.contractingSubgroupIsRadical G hG _ E, hU, heU ▸ hV⟩

private theorem rankOne_of_closedEmbedding {G : AffineAlgebraicGroup F}
    (hG : IsReductive G) {S : ClosedSubgroup G.val} (hS : IsSplitTorus S.group)
    (a : relativeRoots S) (c : Cocharacter S.group) (hc : pairing S.group a.val c = 2)
    (H : AffineAlgebraicGroup F) (matrix : SpecialMatrixPoints H 2) (f : H.val ⟶ G.val)
    (hf : IsClosedImmersion f.hom.hom.left) (A : AdditiveLine F) (xp xn : A.group ⟶ G.val)
    (hp : IsClosedImmersion xp.hom.hom.left) (hn : IsClosedImmersion xn.hom.hom.left)
    (hxp : HasScalarAction S a.val xp) (hxn : HasScalarAction S a.val⁻¹ xn)
    (upper : ∀ (R : TestAlgebra F) (x : R),
      (((matrix.inv.app R) (Matrix.SpecialLinearGroup.transvection
        (i := (⟨0⟩ : Index.{u} 2)) (j := ⟨1⟩) (by decide) x)) :
          GroupPoints H.val R) ≫ f.hom.hom = rootPoint xp R x)
    (lower : ∀ (R : TestAlgebra F) (x : R),
      (((matrix.inv.app R) (Matrix.SpecialLinearGroup.transvection
        (i := (⟨1⟩ : Index.{u} 2)) (j := ⟨0⟩) (by decide) x)) :
          GroupPoints H.val R) ≫ f.hom.hom = rootPoint xn R x)
    (diagonal : ∀ (R : TestAlgebra F) (v : Rˣ), ∃ x : GroupPoints H.val R,
      x ≫ f.hom.hom = cocharacterPoint (c ≫ S.inclusion) R v ∧
      (matrix.hom.app R x).val = Matrix.diagonal (fun i : Index.{u} 2 =>
        if i.down = 0 then (v : R) else (↑v⁻¹ : R))) :
    ∃ L : RankOne S, IsRankOneAt S a L := by
  let U : ClosedSubgroup G.val := ⟨A.group, xp, hp⟩
  let V : ClosedSubgroup G.val := ⟨A.group, xn, hn⟩
  let L : RankOne S :=
    { group := H
      matrix := matrix
      embedding := f
      closedEmbedding := hf
      trivialKernel := by
        haveI := mono_over _ hf
        apply IsPullback.of_vert_isIso_mono
        exact ⟨by rw [Category.id_comp, IsMonHom.one_hom]⟩
      positive := U
      negative := V
      additive := A
      upper := Iso.refl _
      lower := Iso.refl _
      cochar := c
      upperFormula := by
        intro R x
        change _ = rootPoint (𝟙 A.group ≫ xp) R x
        rw [Category.id_comp]
        exact upper R x
      lowerFormula := by
        intro R x
        change _ = rootPoint (𝟙 A.group ≫ xn) R x
        rw [Category.id_comp]
        exact lower R x
      diagonalFormula := diagonal }
  have hpos : HasScalarAction S a.val (L.upper.hom ≫ L.positive.inclusion) := by
    change HasScalarAction S a.val (𝟙 A.group ≫ xp)
    rwa [Category.id_comp]
  have hneg : HasScalarAction S a.val⁻¹ (L.lower.hom ≫ L.negative.inclusion) := by
    change HasScalarAction S a.val⁻¹ (𝟙 A.group ≫ xn)
    rwa [Category.id_comp]
  exact ⟨L, hpos, hneg, rankOne_oppositeRadicals hG hS L a hc hpos hneg⟩

section SplitModel

open Specs.Pinning (BasedRootDatum RootCoordinate SplitBorelPair AttachedDatum PinnedGroup)
open Specs.RationalRealization (Realization)
open Specs.IntegralSemisimpleModel (fibre Model Integers forgetFibrePoint)
open Specs.IntegralRootRelations (upper lower diagonal)
open Classification.IntegralSemisimpleModel (forgetFibrePoint_bijective)
open private rankOneFibre rankOneFibre_apply forgetFibrePoint_comp
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Classification.IntegralSemisimpleModel
open private integralCocharacter_point from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.QuasiSplitOrbitLevis
open private cocharacterPoint_postcompose from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.RootData.OrderedRootProducts
open private rankOne_pivot_factorization exists_rankOne_pivots_after_injective_extension
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Classification.IntegralRankOneExtension
open private torus_subgroupOf_centralizer from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.RootData.BorelsAndChambers
open private characterValue_pullback from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Classification.CentralIsogenies
open private pinnedLift from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Classification.PinnedEquivalence

attribute [local instance] Specs.IntegralSemisimpleModel.integerAlgebra

/-- The determinant-one point map on the split model carries all three markings. -/
private theorem integralRankOneMarks (D : BasedRootDatum.{u}) (M : Model D) (i : D.I) :
    ∃ (A : AdditiveLine F) (P : Realization D A)
      (x : ∀ j : D.I, RootCoordinate A P.pinned.pair.T
        (P.pinned.roots (P.datumIso.val.indexEquiv j)).val (P.datumIso.val.indexEquiv j).val)
      (f : IntegralFibreReductivity.rankOnePoints F ⟶
        (groupPointsFunctor F).obj P.pinned.pair.G.val),
      (∀ (R : TestAlgebra F) (z : R),
        f.app R (upper z) =
          rootPoint ((x i).val.hom ≫ (P.pinned.roots (P.datumIso.val.indexEquiv i)).val.inclusion) R z) ∧
      (∀ (R : TestAlgebra F) (z : R),
        let j := D.datum.reflectionPerm i i
        f.app R (lower z) =
          rootPoint ((x j).val.hom ≫ (P.pinned.roots (P.datumIso.val.indexEquiv j)).val.inclusion) R z) ∧
      letI := P.attached.comm
      ∀ (R : TestAlgebra F) (v : Rˣ), f.app R (diagonal v) =
        cocharacterPoint ((P.datumIso.val.coweightEquiv.symm (D.datum.coroot i)).toMul ≫
          P.pinned.pair.T.inclusion) R v := by
  obtain ⟨A, P, e, t, x, ht, _, hT, hx⟩ := M.fieldFibre F
  let g := rankOneFibre (k := F) M.toIntegralMarking i
  let f := g ≫ (groupPointsFunctor F).map e.hom
  have hi : e.hom.hom.hom ≫ e.inv.hom.hom = 𝟙 ((fibre F).obj M.group).X :=
    ((Grp.forget (SchemeOver F)).mapIso e).hom_inv_id
  refine ⟨A, P, x, f, ?_, ?_, ?_⟩
  · intro R z
    haveI : IsIso e.inv.hom.hom := (Grp.forget (SchemeOver F)).map_isIso e.inv
    apply (cancel_mono e.inv.hom.hom).mp
    change ((g.app R (upper z) : GroupPoints ((fibre F).obj M.group) R) ≫ e.hom.hom.hom) ≫
      e.inv.hom.hom = _
    rw [Category.assoc, hi, Category.comp_id]
    apply (forgetFibrePoint_bijective M.group R).injective
    rw [rankOneFibre_apply, ← rootPoint_comp]
    exact (M.rankOneUpper i (CommAlgCat.of Integers.{u} R) z).trans (hx i R z).symm
  · intro R z
    let j := D.datum.reflectionPerm i i
    haveI : IsIso e.inv.hom.hom := (Grp.forget (SchemeOver F)).map_isIso e.inv
    apply (cancel_mono e.inv.hom.hom).mp
    change ((g.app R (lower z) : GroupPoints ((fibre F).obj M.group) R) ≫ e.hom.hom.hom) ≫
      e.inv.hom.hom = _
    rw [Category.assoc, hi, Category.comp_id]
    apply (forgetFibrePoint_bijective M.group R).injective
    rw [rankOneFibre_apply, ← rootPoint_comp]
    exact (M.rankOneLower i (CommAlgCat.of Integers.{u} R) z).trans (hx j R z).symm
  · letI := P.attached.comm
    intro R v
    let c : Cocharacter P.pinned.pair.T.group :=
      (P.datumIso.val.coweightEquiv.symm (D.datum.coroot i)).toMul
    haveI : IsIso e.inv.hom.hom := (Grp.forget (SchemeOver F)).map_isIso e.inv
    apply (cancel_mono e.inv.hom.hom).mp
    change ((g.app R (diagonal v) : GroupPoints ((fibre F).obj M.group) R) ≫ e.hom.hom.hom) ≫
      e.inv.hom.hom = cocharacterPoint (c ≫ P.pinned.pair.T.inclusion) R v ≫ e.inv.hom.hom
    rw [Category.assoc, hi, Category.comp_id, ← cocharacterPoint_postcompose,
      Category.assoc c P.pinned.pair.T.inclusion e.inv]
    have hs : P.pinned.pair.T.inclusion ≫ e.inv = t.inv ≫ (fibre F).map M.torus := by
      rw [← cancel_epi t.hom, ← Category.assoc, ← ht, Category.assoc, e.hom_inv_id,
        Category.comp_id, Iso.hom_inv_id_assoc]
    rw [hs, ← Category.assoc c, cocharacterPoint_postcompose,
      cocharacterPoint_postcompose]
    apply (forgetFibrePoint_bijective M.group R).injective
    rw [rankOneFibre_apply, forgetFibrePoint_comp, integralCocharacter_point P t hT]
    exact M.rankOneDiagonal i (CommAlgCat.of Integers.{u} R) v

private theorem rankOneMatrix_injective {R S : Type u} [CommRing R] [CommRing S]
    (f : R →+* S) (hf : Function.Injective f) :
    Function.Injective (Matrix.SpecialLinearGroup.map (n := Fin 2) f) := by
  intro x y h
  apply Subtype.ext
  ext i j
  exact hf (congrArg (fun m : Matrix.SpecialLinearGroup (Fin 2) S => m.val i j) h)

private theorem rankOnePointMap_injective_of_chart {G : GroupScheme F}
    (f : IntegralFibreReductivity.rankOnePoints F ⟶ (groupPointsFunctor F).obj G)
    (h : ∀ (R : TestAlgebra F) (x y : Matrix.SpecialLinearGroup (Fin 2) R),
      IsUnit (x.val 0 0) → IsUnit (y.val 0 0) → f.app R x = f.app R y → x = y)
    (R : TestAlgebra F) : Function.Injective (f.app R) := by
  intro x y he
  obtain ⟨S, hS, g, t, hg, hp⟩ := exists_rankOne_pivots_after_injective_extension [x, y]
  letI : Algebra F S := (g.comp (algebraMap F R)).toAlgebra
  let S' := CommAlgCat.of F S
  let a : R ⟶ S' := CommAlgCat.ofHom ⟨g, fun _ => rfl⟩
  let m := Matrix.SpecialLinearGroup.map (n := Fin 2) g
  have hn (z : Matrix.SpecialLinearGroup (Fin 2) R) :
      f.app S' (m z) = mapPoints a (f.app R z) :=
    ConcreteCategory.congr_hom (f.naturality a) z
  have h' : (f.app S').hom (upper t * m x) = (f.app S').hom (upper t * m y) := by
    rw [map_mul, map_mul]
    change _ * f.app S' (m x) = _ * f.app S' (m y)
    rw [hn, hn, he]
  exact rankOneMatrix_injective g hg (mul_left_cancel (h S' _ _ (hp x (by simp))
    (hp y (by simp)) h'))

/-- Distinct marked Gauss triples stay distinct in the ambient big cell. -/
private theorem markedTriples_injective {G : AffineAlgebraicGroup F} (hG : IsReductive G)
    (T : ClosedSubgroup G.val) (hT : IsSplitTorus T.group) (b : Character T.group)
    (c : Cocharacter T.group) (hc : pairing T.group b c = 2)
    (hprim : ∃ a : Character T.group, pairing T.group a c = 1)
    (A : AdditiveLine F) (xp xn : A.group ⟶ G.val)
    (hp : IsClosedImmersion xp.hom.hom.left) (hn : IsClosedImmersion xn.hom.hom.left)
    (hxp : HasScalarAction T b xp) (hxn : HasScalarAction T b⁻¹ xn)
    (R : TestAlgebra F) :
    Function.Injective (fun (p : R × Rˣ × R) =>
      rootPoint xn R p.1 * (cocharacterPoint (c ≫ T.inclusion) R p.2.1 * rootPoint xp R p.2.2)) := by
  letI := hG.1
  letI : ConnectedSpace G.val.X.left := connected_of_geometricallyConnected hG.2.1
  let d := c ≫ T.inclusion
  obtain ⟨C, E, _, _, _, _, _, _, _, _, _, _, hcell, _, _⟩ := CocharacterDynamics.cocharacterDynamics G d
  obtain ⟨u, hu⟩ := torus_subgroupOf_centralizer hT c C
  have hg (r : Rˣ) : cocharacterPoint c R r ≫ u.hom.hom ≫ C.centralizer.inclusion.hom.hom =
      cocharacterPoint d R r := by
    have he : c ≫ (u ≫ C.centralizer.inclusion) = d := congrArg (c ≫ ·) hu
    exact (cocharacterPoint_postcompose c (u ≫ C.centralizer.inclusion) R r).symm.trans
      (congrArg (cocharacterPoint · R r) he)
  have hpos (z : R) : ∃ p : GroupPoints C.contracting.group R,
      p ≫ C.contracting.inclusion.hom.hom = rootPoint xp R z := by
    exact (C.contracting_points R _).mp (rootPoint_hasLimit hxp c (by rw [hc]; decide) R z)
  have hneg (z : R) : ∃ p : GroupPoints E.contracting.group R,
      p ≫ E.contracting.inclusion.hom.hom = rootPoint xn R z := by
    apply (E.contracting_points R _).mp
    have hsign : pairing T.group b⁻¹ (oppositeCocharacter c) = 2 := by
      obtain ⟨hcT, _, _, _, _, P, _, hP⟩ := RootData.CharacterPairing.perfectCharacterPairing T.group hT
      letI := hcT
      rw [oppositeCocharacter_eq_inv, ← hP]
      change P (-Additive.ofMul b) (-Additive.ofMul c) = 2
      simp only [map_neg, LinearMap.neg_apply, neg_neg, hP, hc]
    have h := rootPoint_hasLimit hxn (oppositeCocharacter c) (by rw [hsign]; decide) R z
    have he : oppositeCocharacter c ≫ T.inclusion = oppositeCocharacter d := Category.assoc _ _ _
    exact he ▸ h
  have hmul (n : GroupPoints E.contracting.group R)
      (t : GroupPoints C.centralizer.group R) (p : GroupPoints C.contracting.group R) :
      lift n (lift t p) ≫ CocharacterDynamics.bigCellMap C E =
      (n ≫ E.contracting.inclusion.hom.hom : GroupPoints G.val R) *
        ((t ≫ C.centralizer.inclusion.hom.hom : GroupPoints G.val R) *
          (p ≫ C.contracting.inclusion.hom.hom : GroupPoints G.val R)) := by
    simp only [CocharacterDynamics.bigCellMap, CocharacterDynamics.multiplyFactors, MonObj.comp_mul,
      lift_fst_assoc, lift_snd_assoc]
  have hcpoint : Function.Injective (fun r : Rˣ => cocharacterPoint d R r) := by
    obtain ⟨χ, hχ⟩ := hprim
    haveI : Mono T.inclusion.hom.hom := mono_over _ T.isClosedImmersion
    intro r s hr
    dsimp only [d] at hr
    rw [cocharacterPoint_postcompose, cocharacterPoint_postcompose] at hr
    have hh := congrArg (characterValue χ R) ((cancel_mono T.inclusion.hom.hom).mp hr)
    rw [(RootData.CharacterPairing.characterPairingComposition _ χ c).2 R r,
      (RootData.CharacterPairing.characterPairingComposition _ χ c).2 R s, hχ] at hh
    exact Units.ext (by simpa only [zpow_one] using hh)
  haveI : IsOpenImmersion (CocharacterDynamics.bigCellMap C E).left := hcell
  haveI : Mono (CocharacterDynamics.bigCellMap C E) := Over.mono_of_mono_left _
  haveI : Mono xp.hom.hom := mono_over _ hp
  haveI : Mono xn.hom.hom := mono_over _ hn
  rintro ⟨l, v, r⟩ ⟨l', v', r'⟩ he
  obtain ⟨n, hn'⟩ := hneg l
  obtain ⟨n', hn''⟩ := hneg l'
  obtain ⟨p, hp'⟩ := hpos r
  obtain ⟨p', hp''⟩ := hpos r'
  let t : GroupPoints C.centralizer.group R := cocharacterPoint c R v ≫ u.hom.hom
  let t' : GroupPoints C.centralizer.group R := cocharacterPoint c R v' ≫ u.hom.hom
  have ht₁ : (t ≫ C.centralizer.inclusion.hom.hom : GroupPoints G.val R) =
      cocharacterPoint d R v := (Category.assoc _ _ _).trans (hg v)
  have ht₂ : (t' ≫ C.centralizer.inclusion.hom.hom : GroupPoints G.val R) =
      cocharacterPoint d R v' := (Category.assoc _ _ _).trans (hg v')
  have h : lift n (lift t p) = lift n' (lift t' p') := by
    apply (cancel_mono (CocharacterDynamics.bigCellMap C E)).mp
    rw [hmul n t p, hmul n' t' p', hn', hn'', hp', hp'', ht₁, ht₂]
    exact he
  have hleft : n = n' := by simpa only [lift_fst] using congrArg (· ≫ fst _ _) h
  have hright : lift t p = lift t' p' := by simpa only [lift_snd] using congrArg (· ≫ snd _ _) h
  have ht' : t = t' := by simpa only [lift_fst] using congrArg (· ≫ fst _ _) hright
  have hpp : p = p' := by simpa only [lift_snd] using congrArg (· ≫ snd _ _) hright
  have hl : l = l' := rootPoint_injective_of_mono xn R
    (hn'.symm.trans ((congrArg (· ≫ E.contracting.inclusion.hom.hom) hleft).trans hn''))
  have hv : v = v' := hcpoint (ht₁.symm.trans
    ((congrArg (· ≫ C.centralizer.inclusion.hom.hom) ht').trans ht₂))
  have hr : r = r' := rootPoint_injective_of_mono xp R
    (hp'.symm.trans ((congrArg (· ≫ C.contracting.inclusion.hom.hom) hpp).trans hp''))
  subst l' v' r'
  rfl

private theorem scalarAction_of_torusIso {X Y : GroupScheme F}
    {T : ClosedSubgroup X} {T' : ClosedSubgroup Y}
    (f : X ≅ Y) (t : T.group ≅ T'.group)
    (ht : T.inclusion ≫ f.hom = t.hom ≫ T'.inclusion)
    {A : AdditiveLine F} (x : A.group ⟶ X) (b : Character T'.group)
    (hx : HasScalarAction T (t.hom ≫ b) x) : HasScalarAction T' b (x ≫ f.hom) := by
  intro R s z
  let p : GroupPoints T.group R := s ≫ t.inv.hom.hom
  have ht' : t.inv ≫ T.inclusion ≫ f.hom = T'.inclusion :=
    (congrArg (t.inv ≫ ·) ht).trans (t.inv_hom_id_assoc T'.inclusion)
  have hconj : (p ≫ T.inclusion.hom.hom) ≫ f.hom.hom.hom = s ≫ T'.inclusion.hom.hom := by
    change ((s ≫ t.inv.hom.hom) ≫ T.inclusion.hom.hom) ≫ f.hom.hom.hom = _
    simp only [Category.assoc]
    exact congrArg (fun i : T'.group ⟶ Y => s ≫ i.hom.hom) ht'
  have hval : characterValue (t.hom ≫ b) R p = characterValue b R s := by
    have he : t.inv.hom.hom ≫ t.hom.hom.hom = 𝟙 _ :=
      (Grp.forget (SchemeOver F)).congr_map t.inv_hom_id
    have hv := characterValue_pullback t.hom b R p
    change characterValue (t.hom ≫ b) R p = _ at hv
    rw [hv]
    change characterValue b R ((s ≫ t.inv.hom.hom) ≫ t.hom.hom.hom) = _
    rw [Category.assoc, he, Category.comp_id]
  have h := congrArg (· ≫ f.hom.hom.hom) (hx R p z)
  rw [MonObj.mul_comp, MonObj.mul_comp, GrpObj.inv_comp, hconj, hval,
    ← rootPoint_comp, ← rootPoint_comp] at h
  exact h

private structure AbsoluteRankOneMap {G : AffineAlgebraicGroup F} (T : ClosedSubgroup G.val)
    (b : Character T.group) (c : Cocharacter T.group) where
  additive : AdditiveLine F
  positive : additive.group ⟶ G.val
  negative : additive.group ⟶ G.val
  positiveClosed : IsClosedImmersion positive.hom.hom.left
  negativeClosed : IsClosedImmersion negative.hom.hom.left
  positiveAction : HasScalarAction T b positive
  negativeAction : HasScalarAction T b⁻¹ negative
  points : IntegralFibreReductivity.rankOnePoints F ⟶ (groupPointsFunctor F).obj G.val
  upper_eq : ∀ (R : TestAlgebra F) (z : R), points.app R (upper z) = rootPoint positive R z
  lower_eq : ∀ (R : TestAlgebra F) (z : R), points.app R (lower z) = rootPoint negative R z
  diagonal_eq : ∀ (R : TestAlgebra F) (v : Rˣ),
    points.app R (diagonal v) = cocharacterPoint (c ≫ T.inclusion) R v

private theorem absoluteRankOneMap_exists (P : SplitBorelPair F) (D : AttachedDatum P)
    (b : Root P.T) :
    letI := D.comm
    Nonempty (AbsoluteRankOneMap P.T b.val (D.datum.rootDatum.coroot b).toMul) := by
  letI := D.comm
  obtain ⟨M⟩ := Classification.IntegralRealization.integralRealization D.toBased
  obtain ⟨A, Q, x, f, hupper, hlower, hdiag⟩ := integralRankOneMarks (F := F) D.toBased M b
  obtain ⟨U, ⟨p⟩⟩ := Classification.Pinning.pinningsExist A P
  let P' : PinnedGroup A := ⟨P, U, p⟩
  let u : D.toBased ⟶ Q.attached.toBased := Q.datumIso
  let v : Q.attached.toBased ⟶ D.toBased := Pinning.basedRootDatumGroupoid.inv u
  obtain ⟨e, he⟩ := pinnedLift Q.pinned P' Q.attached D v
  let j := D.datum.rootDatum.reflectionPerm b b
  let r (i : Root P.T) := Q.datumIso.val.indexEquiv i
  let m (i : Root P.T) : A.group ⟶ Q.pinned.pair.G.val :=
    (x i).val.hom ≫ (Q.pinned.roots (r i)).val.inclusion
  have hcomp (i : Root P.T) : e.torus.hom ≫ i.val = (r i).val := by
    have he' := congrArg (fun g : Q.attached.toBased ⟶ D.toBased => g.val.indexEquiv (r i)) he
    change (Classification.Pinning.inducedBasedIso e Q.attached D).val.indexEquiv (r i) =
      u.val.indexEquiv.symm (r i) at he'
    have hi : e.torus.inv ≫ (r i).val = i.val :=
      congrArg Subtype.val (he'.trans (Q.datumIso.val.indexEquiv.symm_apply_apply i))
    rw [← hi, Iso.hom_inv_id_assoc]
  have hj : j.val = b.val⁻¹ := by
    apply Additive.ofMul.injective
    change Additive.ofMul (D.datum.rootDatum.reflectionPerm b b).val = -Additive.ofMul b.val
    rw [← D.datum.root_eq, ← D.datum.root_eq, RootPairing.root_reflectionPerm,
      RootPairing.reflection_apply_self]
  have hclosed (i : Root P.T) : IsClosedImmersion (m i ≫ e.group.hom).hom.hom.left := by
    haveI : IsIso (x i).val.hom.hom.hom.left :=
      (Grp.forget (SchemeOver F) ⋙ Over.forget _).map_isIso (x i).val.hom
    haveI : IsClosedImmersion (Q.pinned.roots (r i)).val.inclusion.hom.hom.left :=
      (Q.pinned.roots (r i)).val.isClosedImmersion
    haveI : IsIso e.group.hom.hom.hom.left :=
      (Grp.forget (SchemeOver F) ⋙ Over.forget _).map_isIso e.group.hom
    change IsClosedImmersion (((x i).val.hom.hom.hom.left ≫
      (Q.pinned.roots (r i)).val.inclusion.hom.hom.left) ≫ e.group.hom.hom.hom.left)
    infer_instance
  have hact (i : Root P.T) : HasScalarAction P.T i.val (m i ≫ e.group.hom) :=
    scalarAction_of_torusIso e.group e.torus e.torus_comm (m i) i.val
      ((hcomp i).symm ▸ (x i).property)
  letI := Q.attached.comm
  let c : Cocharacter P.T.group := (D.datum.rootDatum.coroot b).toMul
  let q : Cocharacter Q.pinned.pair.T.group :=
    (Q.datumIso.val.coweightEquiv.symm (D.datum.rootDatum.coroot b)).toMul
  have hq : q ≫ e.torus.hom = c := by
    have h := congrArg (fun g : Q.attached.toBased ⟶ D.toBased =>
      g.val.coweightEquiv (D.datum.rootDatum.coroot b)) he
    change Additive.ofMul (c ≫ e.torus.inv) = Additive.ofMul q at h
    have h' : c ≫ e.torus.inv = q := Additive.ofMul.injective h
    rw [← h', Category.assoc, e.torus.inv_hom_id, Category.comp_id]
  refine ⟨⟨A, m b ≫ e.group.hom, m j ≫ e.group.hom, hclosed b, hclosed j, hact b,
    hj ▸ hact j, f ≫ (groupPointsFunctor F).map e.group.hom, ?_, ?_, ?_⟩⟩
  · intro R z
    change f.app R (upper z) ≫ e.group.hom.hom.hom = _
    rw [hupper]
    exact (rootPoint_comp (m b) e.group.hom R z).symm
  · intro R z
    change f.app R (lower z) ≫ e.group.hom.hom.hom = rootPoint (m j ≫ e.group.hom) R z
    rw [hlower]
    exact (rootPoint_comp (m j) e.group.hom R z).symm
  · intro R v
    change f.app R (diagonal v) ≫ e.group.hom.hom.hom = cocharacterPoint (c ≫ P.T.inclusion) R v
    rw [show f.app R (diagonal v) = cocharacterPoint (q ≫ Q.pinned.pair.T.inclusion) R v
      from hdiag R v, ← cocharacterPoint_postcompose]
    have h : (q ≫ Q.pinned.pair.T.inclusion) ≫ e.group.hom = c ≫ P.T.inclusion := by
      rw [Category.assoc q, e.torus_comm, ← Category.assoc q, hq]
    exact congrArg (cocharacterPoint · R v) h

private theorem AbsoluteRankOneMap.injective {G : AffineAlgebraicGroup F} (hG : IsReductive G)
    {T : ClosedSubgroup G.val} (hT : IsSplitTorus T.group)
    {b : Character T.group} {c : Cocharacter T.group} (hc : pairing T.group b c = 2)
    (hprim : ∃ χ : Character T.group, pairing T.group χ c = 1)
    (M : AbsoluteRankOneMap T b c) (R : TestAlgebra F) :
    Function.Injective (M.points.app R) := by
  apply rankOnePointMap_injective_of_chart
  intro S x y hx hy he
  let factors (m : Matrix.SpecialLinearGroup (Fin 2) S) (v : Sˣ) :
      S × Sˣ × S := (m.val 1 0 * ↑v⁻¹, v, m.val 0 1 * ↑v⁻¹)
  have hmark (m : Matrix.SpecialLinearGroup (Fin 2) S) (v : Sˣ) (hv : (v : S) = m.val 0 0) :
      M.points.app S m =
        rootPoint M.negative S (factors m v).1 *
          (cocharacterPoint (c ≫ T.inclusion) S (factors m v).2.1 *
            rootPoint M.positive S (factors m v).2.2) := by
    change (M.points.app S).hom m = _
    refine (congrArg (M.points.app S).hom (rankOne_pivot_factorization m v hv)).trans ?_
    rw [map_mul, map_mul]
    change M.points.app S (lower _) * M.points.app S (diagonal _) *
        M.points.app S (upper _) = _
    rw [M.lower_eq, M.diagonal_eq, M.upper_eq, mul_assoc]
  have ht := (markedTriples_injective hG T hT b c hc hprim M.additive M.positive M.negative
    M.positiveClosed M.negativeClosed M.positiveAction M.negativeAction S)
    ((hmark x hx.unit hx.unit_spec).symm.trans (he.trans (hmark y hy.unit hy.unit_spec)))
  have hparam := congrArg (fun p : S × Sˣ × S => lower p.1 * diagonal p.2.1 * upper p.2.2) ht
  exact (rankOne_pivot_factorization x hx.unit hx.unit_spec).trans
    (hparam.trans (rankOne_pivot_factorization y hy.unit hy.unit_spec).symm)

end SplitModel

section Singleton

open IntegralRootRelations (upper lower diagonal)
open Specs.Arithmetic.LocalMixingMarkedMatrixDescent (liftMatrix)
open private actualDatum_unique from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Classification.TransportedRootCoordinates
open private baseChange_rootPoint from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.LocalMixingMarkedMatrixDescent

private theorem inverse_restriction {K : Type u} [Field K] [Algebra F K]
    {X Y : GroupScheme F} (i : X ⟶ Y) (a : Character X)
    (b : Character ((groupBaseChange F K).obj Y)) (e : MultiplicativeComparison F K)
    (h : (groupBaseChange F K).map i ≫ b = (groupBaseChange F K).map a ≫ e.inv) :
    (groupBaseChange F K).map i ≫ b⁻¹ = (groupBaseChange F K).map a⁻¹ ≫ e.inv := by
  have hb : (baseChange F K).map i.hom.hom ≫ b.hom.hom =
      (baseChange F K).map a.hom.hom ≫ e.inv.hom.hom :=
    congrArg (fun f : Character ((groupBaseChange F K).obj X) => f.hom.hom) h
  apply Grp.hom_ext
  change (baseChange F K).map i.hom.hom ≫ b⁻¹.hom.hom =
    (baseChange F K).map a⁻¹.hom.hom ≫ e.inv.hom.hom
  rw [Grp.Hom.hom_hom_inv, Grp.Hom.hom_hom_inv, Functor.map_inv', GrpObj.comp_inv]
  have hpost := GrpObj.inv_comp
    (G := ((groupBaseChange F K).obj (multiplicativeGroupAlgebra F).val).X)
    ((groupBaseChange F K).map a).hom.hom e.inv.hom.hom
  exact (congrArg (·⁻¹) hb).trans hpost.symm

/-- A singleton absolute fibre supplies the marked split rank-one subgroup at the
given relative root. -/
theorem singletonRootSL2 : SingletonRootSL2.{u} := by
  intro F _ _ _ _ G hsimple hsc S hS a ha
  obtain ⟨T, i, hTorus, hTmax, hi, K, hK, hAlg, hFin, hGal, hT, e, hGK, hTK, he, ha⟩ := ha
  letI := hK
  letI := hAlg
  letI := hFin
  letI := hGal
  let E := groupBaseChange F K
  let GK := baseChangedAlgebraicGroup K G
  let TK := baseChangedSubgroup K T hT
  have hG := reductive_of_semisimple G hsimple.1
  have hm : IsGeometricallyMaximal TK :=
    geometricallyMaximal_baseChange G hG T hTorus hTmax hTK
  obtain ⟨hcomm, D, b, c, hres, hfixed, hcor, hc, l, hl⟩ :=
    singletonCoroot_data hsimple.1 hsc hS hTorus hTmax i hi hT hGK hTK e he a.val ha
  letI : IsCommMonObj TK.group.X := hcomm
  let P := splitBorelPair GK hGK.1 TK hTK hm
  let A := Classification.Pinning.attachedDatum P
  letI : IsCommMonObj P.T.group.X := A.comm
  have hD : D = A.datum := actualDatum_unique hGK.1 hTK hm D A.datum
  rw [hD] at hcor hl
  let cK : Cocharacter TK.group := (A.datum.rootDatum.coroot b).toMul
  have hpair : pairing TK.group b.val cK = 2 := by
    refine (A.datum.pairing_eq b.val cK).symm.trans ?_
    change A.datum.rootDatum.toLinearMap (Additive.ofMul b.val) (A.datum.rootDatum.coroot b) = 2
    rw [← A.datum.root_eq b]
    exact A.datum.rootDatum.coroot_root_two b
  let χ : Character TK.group := (A.datum.rootDatum.toPerfPair.symm l).toMul
  have hχ : pairing TK.group χ cK = 1 := by
    refine (A.datum.pairing_eq χ cK).symm.trans ?_
    change A.datum.rootDatum.toPerfPair (A.datum.rootDatum.toPerfPair.symm l)
      (A.datum.rootDatum.coroot b) = 1
    rw [LinearEquiv.apply_symm_apply]
    exact hl
  have hcorK : e.hom ≫ E.map (c ≫ i) = cK := congrArg Additive.toMul hcor
  have hdiagK : cK ≫ TK.inclusion = e.hom ≫ E.map (c ≫ S.inclusion) := by
    change cK ≫ E.map T.inclusion = _
    rw [← hcorK, Category.assoc, ← E.map_comp, Category.assoc, hi]
  obtain ⟨M⟩ := absoluteRankOneMap_exists P A b
  change AbsoluteRankOneMap (G := GK) TK b.val cK at M
  obtain ⟨β, hβ⟩ := invariantCharacter_descends T e he b.val (fun σ => (hfixed σ).1)
  have hnormalize := LocalMixingRootMarkNormalization.rootMarkNormalization F K G T hT
    hGK.1 hTK hm e he β
  dsimp only at hnormalize
  rw [hβ] at hnormalize
  obtain ⟨A₀, j, yPlus, yMinus, hj, hyPlus, hyMinus, haPlus, haMinus, m, hinj, hu, hlower, hd⟩ :=
    hnormalize b.property M.additive M.positive M.negative M.positiveClosed M.negativeClosed
      M.positiveAction M.negativeAction (cK ≫ TK.inclusion) M.points
      (M.injective hGK.1 hTK hpair ⟨χ, hχ⟩) M.upper_eq M.lower_eq M.diagonal_eq
  have hres' := inverse_restriction i a.val b.val e hres
  have hp := scalarAction_of_baseChange hi hT e he a.val b.val hres yPlus
    (j.inv ≫ E.map yPlus) haPlus (baseChange_rootPoint j hj yPlus)
  have hn := scalarAction_of_baseChange hi hT e he a.val⁻¹ b.val⁻¹ hres' yMinus
    (j.inv ≫ E.map yMinus) haMinus (baseChange_rootPoint j hj yMinus)
  have hd' (R : TestAlgebra K) (v : Rˣ) :
      m.app R (diagonal v) = cocharacterPoint (e.hom ≫ E.map (c ≫ S.inclusion)) R v :=
    (hd R v).trans (congrArg (cocharacterPoint · R v) hdiagK)
  obtain ⟨operations, matrix, f, hf, _, hUpper, hLower, hDiag, _⟩ :=
    LocalMixingMarkedMatrixDescent.markedMatrixDescent G A₀ M.additive j e hj he yPlus yMinus
      (c ≫ S.inclusion) hyPlus hyMinus m hinj hu hlower hd'
  let H := @Specs.StandardGroups.spectrum F _ (Specs.StandardGroups.SLCoordinates F (Index.{u} 2))
    _ operations.hopf inferInstance
  refine rankOne_of_closedEmbedding hG hS.1 a c hc H matrix f hf A₀ yPlus yMinus
    hyPlus hyMinus hp hn ?_ ?_ ?_
  · intro R z
    have h : liftMatrix (upper z) = Matrix.SpecialLinearGroup.transvection
        (i := (⟨0⟩ : Index.{u} 2)) (j := ⟨1⟩) (by decide) z := by
      apply Subtype.ext
      ext ⟨i⟩ ⟨j⟩
      fin_cases i <;> fin_cases j <;>
        simp [liftMatrix, upper, Matrix.SpecialLinearGroup.transvection_coe]
    rw [← h]
    exact hUpper R z
  · intro R z
    have h : liftMatrix (lower z) = Matrix.SpecialLinearGroup.transvection
        (i := (⟨1⟩ : Index.{u} 2)) (j := ⟨0⟩) (by decide) z := by
      apply Subtype.ext
      ext ⟨i⟩ ⟨j⟩
      fin_cases i <;> fin_cases j <;>
        simp [liftMatrix, lower, Matrix.SpecialLinearGroup.transvection_coe]
    rw [← h]
    exact hLower R z
  · intro R v
    let x : GroupPoints H.val R := matrix.inv.app R (liftMatrix (diagonal v))
    have hx : matrix.hom.app R x = liftMatrix (diagonal v) :=
      GrpCat.hom_inv_apply (matrix.app R) _
    refine ⟨x, hDiag R v, ?_⟩
    rw [hx]
    ext ⟨i⟩ ⟨j⟩
    fin_cases i <;> fin_cases j <;> simp [liftMatrix, diagonal]


theorem splitCase : SplitCase.{u} := by
  intro F _ _ _ _ G hsimple hsc hsplit S hS
  have hm := geometricallyMaximal_of_maximalSplit hsplit S hS
  refine ⟨hm, ?_⟩
  intro a
  have h := singleAbsoluteRoot_of_split S hsplit.1 hS.1 hm a
  obtain ⟨L, hL⟩ := singletonRootSL2 F G hsimple hsc S hS a h
  exact ⟨h, L, hL,
    isRootSubgroup_of_scalarAction S L.positive _ L.additive L.upper hL.1,
    isRootSubgroup_of_scalarAction S L.negative _ L.additive L.lower hL.2.1⟩
end Singleton

end

end LinearAlgebraicGroups.Arithmetic.LocalMixingSingletonRootSL2
