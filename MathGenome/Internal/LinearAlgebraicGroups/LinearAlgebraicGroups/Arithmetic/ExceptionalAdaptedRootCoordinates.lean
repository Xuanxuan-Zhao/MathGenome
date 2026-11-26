import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Arithmetic.ExceptionalAdaptedRootCoordinates
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.ExceptionalAdaptedPinnedOuterComparison
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.ExceptionalAdaptedRationalOppositePair
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.ExceptionalPinnedBaseChange
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.ExceptionalInnerIndices
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Descent.RelativeRank
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Relative.RelativeChambers
import Batteries.Tactic.OpenPrivate

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open CategoryTheory.CartesianMonoidalCategory CategoryTheory.MonoidalCategory
open scoped CategoryTheory.MonObj

universe u

namespace LinearAlgebraicGroups.Arithmetic.ExceptionalAdaptedRootCoordinates

open LinearAlgebraicGroups.Specs
open Specs.ExceptionalAdaptedRootCoordinates
open Specs.CharacterDescent (Character)
open Specs.ExceptionalAffineBruhat (ExceptionalNumbering FieldPoints)
open Specs.ExceptionalInnerIndices (HasInnerIndex IsSplitOfRank)
open Specs.ExceptionalInnerStandardTorusDescent (markedCharacter)
open Specs.ExceptionalIwahoriImageComparison (markedGroundPoint)
open Specs.ExceptionalMarkedRootDescent (MarkedFibre)
open Specs.GeometricRadicals (IsMaximalTorus IsSplitTorus)
open Specs.IntegralSemisimpleModel (Model)
open Specs.Pinning (BasedRootDatum)
open Specs.Relative.MaximalSplitTori (IsMaximalSplitTorus IsMinimalParabolic)
open Specs.RelativeRank (relativeRank)
open Specs.SchemeDerivedGroup (IsSubgroupOf)

noncomputable section

set_option backward.isDefEq.respectTransparency false

open private dimension_of_iso split_dimension_le_rank standard_torus_dimension split_baseChange_dimension
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Descent.RelativeRank

private theorem relativeRank_eq_of_bound {F : Type u} [Field F] (G : AffineAlgebraicGroup F)
    {S : ClosedSubgroup G.val} {r : ℕ} (hS : IsSplitOfRank S.group r)
    (hbound : ∀ (T : ClosedSubgroup G.val) (s : ℕ), IsSplitOfRank T.group s → s ≤ r) :
    relativeRank G = r := by
  have hd {T : GroupScheme F} {s : ℕ} (h : IsSplitOfRank T s) :
      topologicalKrullDim T.X.left = (s : WithBot ℕ∞) := by
    obtain ⟨e⟩ := h
    exact (dimension_of_iso e).trans (standard_torus_dimension s)
  apply le_antisymm
  · apply iSup_le
    rintro ⟨T, s, hs⟩
    rw [hd hs]
    exact_mod_cast hbound T s hs
  · rw [← hd hS]
    exact split_dimension_le_rank G S ⟨r, hS⟩

open private factor_of_baseChange from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Affine.ClosedSubgroups
open private factor_group_through_subgroup conjugationIso conjugation_apply
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Reductive.GeometricBorelConjugacy
open private conjugates_of_normalizes from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.RootData.BorelNormalizer
open private inclusion_mono from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Reductive.MaximalToriConjugate

private theorem subgroupOf_of_baseChange {F K : Type u} [Field F] [Field K] [Algebra F K]
    {G : GroupScheme F} (T J : ClosedSubgroup G)
    (f : (groupBaseChange F K).obj T.group ⟶ (groupBaseChange F K).obj J.group)
    (hf : f ≫ (groupBaseChange F K).map J.inclusion = (groupBaseChange F K).map T.inclusion) :
    IsSubgroupOf T J := by
  letI := J.isClosedImmersion
  obtain ⟨j, hj⟩ := factor_of_baseChange K T.inclusion.hom.hom J.inclusion.hom.hom f.hom.hom
    (congrArg (fun p => p.hom.hom) hf)
  exact factor_group_through_subgroup J T.inclusion j hj

variable {F : Type u} [Field F] {K : Type u} [Field K] [Algebra F K]
variable {G : AffineAlgebraicGroup F} {D : BasedRootDatum.{u}} {M : Model D}
variable {n r : ℕ} {black : Set (Fin n)}

/-- The two inclusion squares and the root restrictions on the actual finite fibre,
before passing to the separable closure. -/
private theorem finiteInnerChart
    (C : MarkedFibre M K) (b : Fin n ≃ D.base.support)
    (f : C.realization.pinned.pair.G.val ≅ (groupBaseChange F K).obj G.val)
    (N : Set (FieldPoints M K))
    (hN : ∀ (g : 𝟙_ (SchemeOver K) ⟶ C.realization.pinned.pair.G.val.X),
      markedGroundPoint C g ∈ N → Normalizes C.realization.pinned.pair.T.inclusion g)
    (h : HasInnerIndex b r black C f N) :
    let P := C.realization.pinned.pair
    let B := groupBaseChange F K
    ∃ (T S J : ClosedSubgroup G.val) (i : S.group ⟶ T.group)
      (g : 𝟙_ (SchemeOver K) ⟶ P.G.val.X)
      (t : B.obj T.group ≅ P.T.group) (p : P.B.group ⟶ B.obj J.group),
      IsMaximalTorus T ∧ IsMaximalSplitTorus S ∧ IsMinimalParabolic G J ∧
      i ≫ T.inclusion = S.inclusion ∧ IsSubgroupOf T J ∧
      IsSplitOfRank S.group r ∧ relativeRank G = r ∧ markedGroundPoint C g ∈ N ∧
      (let a := (conjugationIso g).symm ≪≫ f
       t.hom ≫ P.T.inclusion ≫ a.hom = B.map T.inclusion ∧
       p ≫ B.map J.inclusion = P.B.inclusion ≫ a.hom) ∧
      ∀ j, j ∈ black ↔ (B.map i ≫ t.hom ≫ markedCharacter C (b j)) = 1 := by
  obtain ⟨hbound, T, S, t₀, hT, hS, hr, ⟨i, hi⟩, ht₀, g, J, s, p, hg, hJ, _, hs, hp, hblack⟩ := h
  let P := C.realization.pinned.pair
  let B := groupBaseChange F K
  let c := conjugationIso g
  obtain ⟨t', ht'⟩ := conjugates_of_normalizes P.T (hN g hg)
  have hc : t'.hom ≫ P.T.inclusion = P.T.inclusion ≫ c.hom := by
    apply Grp.hom_ext
    exact ht'.trans (conjugation_apply g P.T.inclusion.hom.hom).symm
  let a := c.symm ≪≫ f
  let t := t₀ ≪≫ t'
  have ht : t.hom ≫ P.T.inclusion ≫ a.hom = B.map T.inclusion := by
    change (t₀.hom ≫ t'.hom) ≫ P.T.inclusion ≫ c.inv ≫ f.hom = _
    simpa only [Category.assoc, reassoc_of% hc, c.hom_inv_id_assoc] using ht₀
  have hpa : p ≫ B.map J.inclusion = P.B.inclusion ≫ a.hom := by
    apply (cancel_mono f.inv).mp
    simp only [Category.assoc, a, Iso.trans_hom, Iso.symm_hom, f.hom_inv_id, Category.comp_id]
    apply Grp.hom_ext
    change (p ≫ B.map J.inclusion ≫ f.inv).hom.hom =
      P.B.inclusion.hom.hom ≫ c.inv.hom.hom
    rw [hp]
    change _ = P.B.inclusion.hom.hom ≫ (conjugationIso g⁻¹).hom.hom.hom
    have hh := conjugation_apply g⁻¹ P.B.inclusion.hom.hom
    change P.B.inclusion.hom.hom ≫ (conjugationIso g⁻¹).hom.hom.hom = _ at hh
    rw [hh, GrpObj.comp_inv, inv_inv]
  obtain ⟨j, hj⟩ := P.containsTorus
  have hTJ : IsSubgroupOf T J := by
    apply subgroupOf_of_baseChange (K := K) T J (t.hom ≫ j ≫ p)
    change (t.hom ≫ j ≫ p) ≫ B.map J.inclusion = B.map T.inclusion
    rw [Category.assoc, Category.assoc, hpa, ← Category.assoc j, hj, ht]
  have hst : B.map i ≫ t.hom = s := by
    letI := inclusion_mono P.T
    apply (cancel_mono P.T.inclusion).mp
    apply Grp.hom_ext
    change ((B.map i ≫ t.hom) ≫ P.T.inclusion).hom.hom = (s ≫ P.T.inclusion).hom.hom
    rw [hs]
    have hmap : B.map i ≫ t₀.hom ≫ P.T.inclusion = B.map S.inclusion ≫ f.inv := by
      apply (cancel_mono f.hom).mp
      have ht₀' : t₀.hom ≫ P.T.inclusion ≫ f.hom = B.map T.inclusion := ht₀
      rw [Category.assoc, Category.assoc, ht₀', Category.assoc, Iso.inv_hom_id, Category.comp_id,
        ← Functor.map_comp, hi]
    have heq : (B.map i ≫ t.hom) ≫ P.T.inclusion = (B.map S.inclusion ≫ f.inv) ≫ c.hom := by
      change (B.map i ≫ t₀.hom ≫ t'.hom) ≫ P.T.inclusion = _
      rw [Category.assoc, Category.assoc, hc, ← Category.assoc (B.map i),
        ← Category.assoc (B.map i ≫ t₀.hom)]
      exact congrArg (fun h => h ≫ c.hom) (by simpa only [Category.assoc] using hmap)
    rw [heq]
    change (B.map S.inclusion ≫ f.inv).hom.hom ≫ c.hom.hom.hom = _
    exact conjugation_apply g _
  refine ⟨T, S, J, i, g, t, p, hT, hS, hJ, hi, hTJ, hr,
    relativeRank_eq_of_bound G hr hbound, hg, ⟨ht, hpa⟩, fun j => ?_⟩
  rw [← Category.assoc, hst, hblack]
  exact ⟨fun h => Grp.hom_ext _ _ h, fun h => congrArg (fun v => v.hom.hom) h⟩

section SplitFibreComparison

open Opposite
open Specs.AdjointRepresentation (GroupPoints)
open Specs.ExceptionalIwahoriImageComparison (markedPositiveBorel)
open Specs.ExceptionalMarkedRootDescent (markedFibrePoint integralTestAlgebra)
open Specs.GeometricRadicals (baseChangedSubgroup)
open Specs.IntegralSemisimpleModel (splitTorus IntegralPoints)
open Specs.Unipotent (baseChangedAlgebraicGroup)
open LinearAlgebraicGroups.Arithmetic.ExceptionalIwahoriImageComparison (markedPositiveBorelCoordinates)
open private positiveAndNegativeEnumerations
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.ExceptionalIwahoriImageComparison
open private fibrePointEquiv markedTorusEquiv markedTorusIncl
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.ExceptionalMarkedRootDescent
open private subgroupIso_of_pointwise baseChange_subgroupPoint_iff
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.ExceptionalPinnedPairCompatibility

private theorem markedPoint_torus_iff (C : MarkedFibre M K) (R : TestAlgebra K)
    (p : GroupPoints C.realization.pinned.pair.G.val R) :
    (∃ t : GroupPoints C.realization.pinned.pair.T.group R,
      t ≫ C.realization.pinned.pair.T.inclusion.hom.hom = p) ↔
    ∃ v : IntegralPoints (splitTorus D) ((integralTestAlgebra K).obj R),
      v ≫ M.torus.hom.hom = markedFibrePoint C R p := by
  constructor
  · rintro ⟨t, rfl⟩
    exact ⟨markedTorusEquiv C R t, (markedTorusIncl C R t).symm⟩
  · rintro ⟨v, hv⟩
    obtain ⟨t, rfl⟩ := (markedTorusEquiv C R).surjective v
    refine ⟨t, (fibrePointEquiv C R).injective ?_⟩
    exact (markedTorusIncl C R t).trans hv

private theorem markedPoint_borel_iff (C : MarkedFibre M K) (R : TestAlgebra K)
    (p : GroupPoints C.realization.pinned.pair.G.val R) :
    (∃ x : GroupPoints C.realization.pinned.pair.B.group R,
      x ≫ C.realization.pinned.pair.B.inclusion.hom.hom = p) ↔
    markedFibrePoint C R p ∈ markedPositiveBorel C R := by
  have he (x : GroupPoints C.realization.pinned.pair.B.group R) :
      markedFibrePoint C R (x ≫ C.realization.pinned.pair.B.inclusion.hom.hom) =
        IntegralSemisimpleModel.forgetFibrePoint M.group R
          (x ≫ C.realization.pinned.pair.B.inclusion.hom.hom ≫ C.groupIso.inv.hom.hom) := by
    unfold markedFibrePoint
    rw [Category.assoc]
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨x, (he x).symm⟩
  · rintro ⟨x, hx⟩
    exact ⟨x, (fibrePointEquiv C R).injective ((he x).trans hx)⟩

variable {L : Type u} [Field L] [Algebra K L]

/-- The integral marking comparison identifies the actual Borel and torus
in each split fibre. -/
private theorem markedFibrePairComparison (C₀ : MarkedFibre M K) (C₁ : MarkedFibre M L)
    (j : C₁.realization.pinned.pair.G.val ≅
      (groupBaseChange K L).obj C₀.realization.pinned.pair.G.val)
    (hj : RespectsIntegralMarking C₀ C₁ j) :
    let P₀ := C₀.realization.pinned.pair
    let P₁ := C₁.realization.pinned.pair
    let B := groupBaseChange K L
    ∃ (jT : P₁.T.group ≅ B.obj P₀.T.group) (jB : P₁.B.group ≅ B.obj P₀.B.group),
      P₁.T.inclusion ≫ j.hom = jT.hom ≫ B.map P₀.T.inclusion ∧
      P₁.B.inclusion ≫ j.hom = jB.hom ≫ B.map P₀.B.inclusion := by
  let P₀ := C₀.realization.pinned.pair
  let P₁ := C₁.realization.pinned.pair
  let H := baseChangedAlgebraicGroup L P₀.G
  let T := baseChangedSubgroup L P₀.T
    (baseChangeClosedSubgroup K L P₀.T.inclusion P₀.T.isClosedImmersion)
  let B := baseChangedSubgroup L P₀.B
    (baseChangeClosedSubgroup K L P₀.B.inclusion P₀.B.isClosedImmersion)
  obtain ⟨_, roots, _, hroots⟩ := positiveAndNegativeEnumerations D
  obtain ⟨jT, hT⟩ := subgroupIso_of_pointwise (H := H) P₁.T T j (by
    intro R p
    change _ ↔ ∃ t : GroupPoints ((groupBaseChange K L).obj P₀.T.group) R,
      t ≫ ((groupBaseChange K L).map P₀.T.inclusion).hom.hom = p ≫ j.hom.hom.hom
    rw [baseChange_subgroupPoint_iff, markedPoint_torus_iff C₁, markedPoint_torus_iff C₀, hj R p])
  obtain ⟨jB, hB⟩ := subgroupIso_of_pointwise (H := H) P₁.B B j (by
    intro R p
    change _ ↔ ∃ b : GroupPoints ((groupBaseChange K L).obj P₀.B.group) R,
      b ≫ ((groupBaseChange K L).map P₀.B.inclusion).hom.hom = p ≫ j.hom.hom.hom
    rw [baseChange_subgroupPoint_iff, markedPoint_borel_iff C₁, markedPoint_borel_iff C₀, hj R p,
      markedPositiveBorelCoordinates C₁ _ roots hroots,
      markedPositiveBorelCoordinates C₀ _ roots hroots])
  exact ⟨jT, jB, hT, hB⟩


open Specs.CharacterPairing (characterValue)
open Specs.ExceptionalInnerStandardTorusDescent (IsUnitComparison)
open Specs.DiagonalizableGroups (groupAlgebra IntegerCharacters)
open Specs.IntegralSemisimpleModel (TorusValues torusPoint Integers)
open LinearAlgebraicGroups.RootData.CharacterPairing (characterValuesDetectCharacters)
open private characterValue_extend from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Relative.RelativeChambers
open private affineTorusPointEquiv from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Classification.IntegralSemisimpleModel

private abbrev multiplicativeGroup (E : Type u) [Field E] : GroupScheme E :=
  specGroup (groupAlgebra E IntegerCharacters)

private theorem markedCharacter_evaluation (C : MarkedFibre M K) (R : TestAlgebra K)
    (p : GroupPoints C.realization.pinned.pair.T.group R) (i : D.I)
    (v : TorusValues D ((integralTestAlgebra K).obj R))
    (hv : markedTorusEquiv C R p = torusPoint D ((integralTestAlgebra K).obj R) v) :
    characterValue (markedCharacter C i) R p = (v (Multiplicative.ofAdd (D.datum.root i)) : R) := by
  have h := C.torus_eval R (p ≫ C.torusIso.inv.hom.hom) v hv (D.datum.root i)
  rw [Category.assoc, ← Grp.comp_hom_hom, Iso.inv_hom_id] at h
  change characterValue (markedCharacter C i) R (p ≫ 𝟙 _) = _ at h
  rwa [Category.comp_id] at h

private theorem markedCharacter_baseChange (C₀ : MarkedFibre M K) (C₁ : MarkedFibre M L)
    (j : C₁.realization.pinned.pair.G.val ≅
      (groupBaseChange K L).obj C₀.realization.pinned.pair.G.val)
    (hj : RespectsIntegralMarking C₀ C₁ j)
    (jT : C₁.realization.pinned.pair.T.group ≅
      (groupBaseChange K L).obj C₀.realization.pinned.pair.T.group)
    (hjT : C₁.realization.pinned.pair.T.inclusion ≫ j.hom =
      jT.hom ≫ (groupBaseChange K L).map C₀.realization.pinned.pair.T.inclusion)
    (e : multiplicativeGroup L ≅ (groupBaseChange K L).obj (multiplicativeGroup K))
    (he : IsUnitComparison K L e) (i : D.I) :
    jT.hom ≫ (groupBaseChange K L).map (markedCharacter C₀ i) ≫ e.inv =
      markedCharacter C₁ i := by
  let T₀ := C₀.realization.pinned.pair.T
  let T₁ := C₁.realization.pinned.pair.T
  apply characterValuesDetectCharacters C₁.realization.pinned.pair.split
  intro R p
  let R₀ := (restrictTestAlgebra K L).obj R
  let p₀ := baseChangePoint K L T₀.group.X R (p ≫ jT.hom.hom.hom)
  have hp : markedTorusEquiv C₀ R₀ p₀ = markedTorusEquiv C₁ R p := by
    let _ := M.torusClosed
    let _ : Mono M.torus.hom.hom := Over.mono_of_mono_left _
    apply (cancel_mono M.torus.hom.hom).mp
    rw [← markedTorusIncl, ← markedTorusIncl]
    have h := hj R (p ≫ T₁.inclusion.hom.hom)
    change markedFibrePoint C₀ R₀
      (baseChangePoint K L C₀.realization.pinned.pair.G.val.X R
        ((p ≫ T₁.inclusion.hom.hom) ≫ j.hom.hom.hom)) = _ at h
    have hn := baseChangePointsSchemeNaturality K L T₀.inclusion.hom.hom R
      (p ≫ jT.hom.hom.hom)
    change baseChangePoint K L C₀.realization.pinned.pair.G.val.X R
      ((p ≫ jT.hom.hom.hom) ≫ ((groupBaseChange K L).map T₀.inclusion).hom.hom) =
      p₀ ≫ T₀.inclusion.hom.hom at hn
    rw [Category.assoc, ← Grp.comp_hom_hom, hjT, Grp.comp_hom_hom, ← Category.assoc] at h
    change markedFibrePoint C₀ R₀ (baseChangePoint K L _ R
      ((p ≫ jT.hom.hom.hom) ≫ ((groupBaseChange K L).map T₀.inclusion).hom.hom)) = _ at h
    exact (congrArg (markedFibrePoint C₀ R₀) hn).symm.trans h
  obtain ⟨v, hv⟩ := (affineTorusPointEquiv (k := Integers.{u}) (M := Multiplicative D.X)
    ((integralTestAlgebra L).obj R)).surjective (markedTorusEquiv C₁ R p)
  have hv₀ : markedTorusEquiv C₀ R₀ p₀ = torusPoint D ((integralTestAlgebra K).obj R₀) v :=
    hp.trans hv.symm
  calc
    _ = characterValue ((groupBaseChange K L).map (markedCharacter C₀ i) ≫ e.inv) R
          (p ≫ jT.hom.hom.hom) := by
      unfold characterValue
      rw [Grp.comp_hom_hom, ← Category.assoc]
    _ = characterValue (markedCharacter C₀ i) R₀ p₀ :=
      characterValue_extend (markedCharacter C₀ i) e he R (p ≫ jT.hom.hom.hom)
    _ = (v (Multiplicative.ofAdd (D.datum.root i)) : R) := markedCharacter_evaluation C₀ R₀ p₀ i v hv₀
    _ = _ := (markedCharacter_evaluation C₁ R p i v hv.symm).symm

end SplitFibreComparison

section CharacterExtension

open Specs.ExceptionalInnerStandardTorusDescent (IsUnitComparison)
open private splitTorus_hom_descends groupBaseChange_map_injective
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Reductive.SplitToriConjugacy
open private multiplicativeGroup_isSplitTorus
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.ExceptionalInnerStandardTorusDescent

private def extendCharacterHom {k E : Type u} [Field k] [Field E] [Algebra k E]
    (H : GroupScheme k)
    (e : multiplicativeGroup E ≅ (groupBaseChange k E).obj (multiplicativeGroup k)) :
    Character H →* Character ((groupBaseChange k E).obj H) where
  toFun χ := (groupBaseChange k E).map χ ≫ e.inv
  map_one' := by
    apply Grp.hom_ext
    change (baseChange k E).map ((1 : Character H).hom.hom) ≫ e.inv.hom.hom = _
    rw [show ((1 : Character H).hom.hom) = 1 from rfl, Functor.map_one]
    exact MonObj.one_comp e.inv.hom.hom
  map_mul' χ ψ := by
    letI : MonObj ((baseChange k E).obj (multiplicativeGroup k).X) :=
      inferInstanceAs (MonObj ((groupBaseChange k E).obj (multiplicativeGroup k)).X)
    apply Grp.hom_ext
    change (baseChange k E).map (χ.hom.hom * ψ.hom.hom) ≫ e.inv.hom.hom = _
    rw [Functor.map_mul, MonObj.mul_comp]
    rfl

private theorem extendCharacterHom_injective {k E : Type u} [Field k] [Field E] [Algebra k E]
    (H : GroupScheme k)
    (e : multiplicativeGroup E ≅ (groupBaseChange k E).obj (multiplicativeGroup k)) :
    Function.Injective (extendCharacterHom H e) :=
  fun _ _ h => groupBaseChange_map_injective ((cancel_mono e.inv).mp h)

private theorem extendCharacterHom_surjective {k E : Type u} [Field k] [Field E] [Algebra k E]
    (H : GroupScheme k)
    (e : multiplicativeGroup E ≅ (groupBaseChange k E).obj (multiplicativeGroup k))
    (hH : IsSplitTorus H) :
    Function.Surjective (extendCharacterHom H e) := by
  intro χ
  obtain ⟨h, hh⟩ := splitTorus_hom_descends hH (multiplicativeGroup_isSplitTorus k) (χ ≫ e.hom)
  refine ⟨h, ?_⟩
  change (groupBaseChange k E).map h = χ ≫ e.hom at hh
  change (groupBaseChange k E).map h ≫ e.inv = χ
  rw [hh, Category.assoc, e.hom_inv_id, Category.comp_id]

end CharacterExtension

section ScalarExtension

variable {L : Type u} [Field L] [Algebra K L]

open private groupBaseChangeTowerIso groupBaseChangeTowerIso_fst
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Relative.RationalCocharacter

private theorem scalarExtendedInnerConjugation {H : GroupScheme K}
    (g : 𝟙_ (SchemeOver K) ⟶ H.X) :
    let c := conjugationIso g
    let z : ((groupBaseChange K L).obj H).X ⟶ ((groupBaseChange K L).obj H).X :=
      toUnit _ ≫ scalarExtendedRationalPoint L g
    ((groupBaseChange K L).map c.inv).hom.hom = z⁻¹ * (𝟙 _) * z := by
  let H' := (groupBaseChange K L).obj H
  let c := conjugationIso g
  let z : H'.X ⟶ H'.X := toUnit _ ≫ scalarExtendedRationalPoint L g
  let b : (H.X ⟶ H.X) →* (H'.X ⟶ H'.X) :=
    (baseChange K L).homMonoidHom (X := H.X) (M := H.X)
  have h : c.inv.hom.hom = (toUnit H.X ≫ g)⁻¹ * (𝟙 H.X) * (toUnit H.X ≫ g) := by
    have hh := conjugation_apply g⁻¹ (𝟙 H.X)
    change (𝟙 H.X) ≫ c.inv.hom.hom = _ at hh
    simpa only [Category.id_comp, GrpObj.comp_inv, inv_inv] using hh
  have hz : z = b (toUnit H.X ≫ g) := by
    change toUnit ((baseChange K L).obj H.X) ≫ scalarExtendedRationalPoint L g =
      (baseChange K L).map (toUnit H.X ≫ g)
    rw [scalarExtendedRationalPoint, ← Category.assoc,
      Functor.Monoidal.toUnit_ε (baseChange K L) H.X, ← Functor.map_comp]
  have hid : b (𝟙 H.X) = 𝟙 H'.X := (baseChange K L).map_id H.X
  change b c.inv.hom.hom = z⁻¹ * (𝟙 _) * z
  rw [h, map_mul, map_mul, map_inv, hid, hz]

end ScalarExtension

open LinearAlgebraicGroups.Arithmetic.ExceptionalInnerStandardTorusDescent (unitComparison)
open LinearAlgebraicGroups.Arithmetic.ExceptionalPinnedBaseChange (markedSplitGroupComparison)

private theorem markedCharacter_eq_simple {k : Type u} [Field k]
    (C : MarkedFibre M k) (i : D.base.support) :
    markedCharacter C i = (C.realization.simpleRoot i).val.val := by
  let _ := C.realization.attached.comm
  apply Additive.ofMul.injective
  change C.realization.datumIso.val.weightEquiv (D.datum.root i) =
    Additive.ofMul (C.realization.simpleRoot i).val.val
  rw [← C.realization.attached.datum.root_eq]
  exact RootPairing.Hom.root_weightMap_apply _ _ i.val C.realization.datumIso.val.toHom

open private groupBaseChangeTowerIso groupBaseChangeTowerIso_fst
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Relative.RationalCocharacter

set_option maxHeartbeats 1000000 in
private theorem innerChart_of_coordinates (project : (Fin n → ℤ) → (Fin r → ℤ))
    (hCoordinates : ∀ {F : Type u} [Field F] {G : AffineAlgebraicGroup F}
      {D : BasedRootDatum.{u}} {M : Model D} {C : MarkedFibre M (SeparableClosure F)}
      (b : Fin n ≃ D.base.support) (A : AdaptedBorel G C),
      ExceptionalNumbering D n b → IsSplitOfRank A.S.group r →
      (∀ i, i ∈ black ↔ A.restrictSimple (b i) = 1) →
      HasRootCoordinates A b project) :
    InnerCoordinates.{u} n r black project := by
  intro F K _ _ _ _ _ _ _ _ G D M C₀ b hb f N hN hIndex
  obtain ⟨T, S, J, i, g, t, p, hT, hS, hJ, hi, ⟨l, hl⟩, hr, hRank, hg,
    ⟨ht, hp⟩, hblack⟩ := finiteInnerChart C₀ b f N hN hIndex
  let L := SeparableClosure F
  let e : K →ₐ[F] L := IsSepClosed.lift
  refine ⟨e, ?_⟩
  letI : Algebra K L := e.toRingHom.toAlgebra
  letI : IsScalarTower F K L :=
    IsScalarTower.of_algebraMap_eq fun x => (e.commutes x).symm
  let C : MarkedFibre M L := Classical.choice (ExceptionalMarkedRootDescent.markedFibreExists M L)
  let a := groupBaseChangeTowerIso (k := F) (K := K) (L := L)
  let P₀ := C₀.realization.pinned.pair
  let P := C.realization.pinned.pair
  let E := groupBaseChange F L
  let B := groupBaseChange K L
  let c := conjugationIso g
  let f₀ := c.symm ≪≫ f
  obtain ⟨j, hj⟩ := markedSplitGroupComparison C₀ C
  obtain ⟨jT, jB, hjT, hjB⟩ := markedFibrePairComparison C₀ C j hj
  obtain ⟨v, hv⟩ := unitComparison F L
  have hta : t.hom ≫ P₀.T.inclusion ≫ f₀.hom = (groupBaseChange F K).map T.inclusion := ht
  have hpa : p ≫ (groupBaseChange F K).map J.inclusion = P₀.B.inclusion ≫ f₀.hom := hp
  let ambient : P.G.val ≅ E.obj G.val := j ≪≫ B.mapIso f₀ ≪≫ a.app G.val
  let torus : E.obj T.group ≅ P.T.group := (a.app T.group).symm ≪≫ B.mapIso t ≪≫ jT.symm
  let borel : P.B.group ⟶ E.obj J.group := jB.hom ≫ B.map p ≫ (a.app J.group).hom
  have htower (X Y : GroupScheme F) (q : X ⟶ Y) :
      B.map ((groupBaseChange F K).map q) ≫ (a.app Y).hom =
        (a.app X).hom ≫ E.map q :=
    a.hom.naturality q
  have hT₁ : P.T.inclusion ≫ j.hom = jT.hom ≫ B.map P₀.T.inclusion := hjT
  have hB₁ : P.B.inclusion ≫ j.hom = jB.hom ≫ B.map P₀.B.inclusion := hjB
  have htorus : torus.hom ≫ P.T.inclusion ≫ ambient.hom = E.map T.inclusion := by
    change ((a.app T.group).inv ≫ B.map t.hom ≫ jT.inv) ≫
      P.T.inclusion ≫ j.hom ≫ B.map f₀.hom ≫ (a.app G.val).hom = _
    have hmap := congrArg B.map hta
    rw [Functor.map_comp, Functor.map_comp] at hmap
    simp only [Category.assoc]
    rw [reassoc_of% hT₁, jT.inv_hom_id_assoc, reassoc_of% hmap, htower, Iso.inv_hom_id_assoc]
  have hborel : borel ≫ E.map J.inclusion = P.B.inclusion ≫ ambient.hom := by
    change (jB.hom ≫ B.map p ≫ (a.app J.group).hom) ≫ E.map J.inclusion =
      P.B.inclusion ≫ j.hom ≫ B.map f₀.hom ≫ (a.app G.val).hom
    have hmap := congrArg B.map hpa
    rw [Functor.map_comp, Functor.map_comp] at hmap
    simp only [Category.assoc]
    rw [← htower, reassoc_of% hB₁, reassoc_of% hmap]
  let A : AdaptedBorel G C :=
    ⟨S, T, J, hS, hT, hJ, i, hi, l, hl, ambient, torus, htorus, borel, hborel, v, hv⟩
  have hblack' (k : Fin n) : k ∈ black ↔ A.restrictSimple (b k) = 1 := by
    obtain ⟨w, hw⟩ := unitComparison K L
    let χ := ((groupBaseChange F K).map i ≫ t.hom ≫ markedCharacter C₀ (b k))
    have hm := markedCharacter_baseChange C₀ C j hj jT hjT w hw (b k)
    change k ∈ black ↔
      E.map i ≫ ((a.app T.group).inv ≫ B.map t.hom ≫ jT.inv) ≫ (C.realization.simpleRoot (b k)).val.val = 1
    rw [← markedCharacter_eq_simple, ← hm]
    have hn : E.map i ≫ (a.app T.group).inv =
        (a.app S.group).inv ≫ B.map ((groupBaseChange F K).map i) := by
      rw [← cancel_mono (a.app T.group).hom, Category.assoc, Category.assoc, htower,
        Iso.inv_hom_id_assoc, Iso.inv_hom_id, Category.comp_id]
    simp only [Category.assoc, jT.inv_hom_id_assoc]
    have hχ : B.map χ = B.map ((groupBaseChange F K).map i) ≫ B.map t.hom ≫
        B.map (markedCharacter C₀ (b k)) := by simp only [χ, Functor.map_comp]
    rw [reassoc_of% hn, ← reassoc_of% hχ]
    have hh : k ∈ black ↔ χ = 1 := hblack k
    rw [hh]
    change _ ↔ (a.app S.group).inv ≫ extendCharacterHom _ w χ = 1
    constructor
    · intro h
      rw [h, map_one]
      apply Grp.hom_ext
      exact MonObj.comp_one _
    · intro h
      apply extendCharacterHom_injective _ w
      rw [map_one]
      apply (cancel_epi (a.app S.group).inv).mp
      rw [h]
      apply Grp.hom_ext
      exact (MonObj.comp_one _).symm
  refine ⟨C, A, a, j, g, groupBaseChangeTowerIso_fst, hj, hg, ?_, hr, hRank, hblack',
    hCoordinates b A hb hr hblack'⟩
  have hcancel :
      ambient.hom ≫ (a.app G.val).inv ≫ B.map f.inv = j.hom ≫ B.map c.inv := by
    dsimp only [ambient, Iso.trans_hom, Functor.mapIso_hom]
    rw [Category.assoc, Category.assoc, Iso.hom_inv_id_assoc, ← Functor.map_comp,
      show f₀.hom ≫ f.inv = c.inv by simp [f₀]]
  change (ambient.hom ≫ _ ≫ _).hom.hom = _
  rw [hcancel, Grp.comp_hom_hom, scalarExtendedInnerConjugation g,
    MonObj.comp_mul, MonObj.comp_mul, GrpObj.comp_inv, Category.comp_id, comp_toUnit_assoc]


section CharacterLattices

open scoped TensorProduct
open Specs.CharacterDescent (StandardLattice)
open Specs.DiagonalizableGroups (groupAlgebra groupAlgebraMap IntegerCharacters)
open _root_.LinearAlgebraicGroups.CharacterDescent (standardSplitTorus splitCompositionPairing)
open private splitGroupHomEquiv from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Multiplicative.CharacterDescent
open private latticeCoordinates charactersOfIso from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.RootData.CharacterPairing
open private specGroupMap_comp from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Affine.ClosedSubgroups

private theorem splitCharacterRestriction {k : Type u} [Field k] {H T : GroupScheme k}
    (hH : IsSplitTorus H) (hT : IsSplitTorus T) (i : H ⟶ T)
    (hi : IsClosedImmersion i.hom.hom.left) :
    Function.Surjective (fun χ : Character T => i ≫ χ) := by
  obtain ⟨r, ⟨dH⟩⟩ := hH
  obtain ⟨n, ⟨dT⟩⟩ := hT
  obtain ⟨eH⟩ := standardSplitTorus (k := k) r
  obtain ⟨eT⟩ := standardSplitTorus (k := k) n
  let jH := eH ≪≫ dH.symm
  let jT := eT ≪≫ dT.symm
  obtain ⟨q, hq⟩ := (splitGroupHomEquiv (k := k) (StandardLattice.{u} n)
    (StandardLattice.{u} r)).surjective (jH.hom ≫ i ≫ jT.inv)
  change specGroupMap (groupAlgebraMap k q) = _ at hq
  have hclosed : IsClosedImmersion (specGroupMap (groupAlgebraMap k q)).hom.hom.left := by
    rw [hq]
    change IsClosedImmersion (jH.hom.hom.hom.left ≫ i.hom.hom.left ≫ jT.inv.hom.hom.left)
    let _ : IsIso jH.hom.hom.hom.left :=
      inferInstanceAs (IsIso ((Grp.forget (SchemeOver k) ⋙ Over.forget _).map jH.hom))
    let _ : IsIso jT.inv.hom.hom.left :=
      inferInstanceAs (IsIso ((Grp.forget (SchemeOver k) ⋙ Over.forget _).map jT.inv))
    let _ := hi
    infer_instance
  have hqsurj : Function.Surjective q := by
    classical
    have h := (hopfMapClosedImmersion k (groupAlgebraMap k q)).mp hclosed
    intro v
    obtain ⟨b, hb⟩ := h (MonoidAlgebra.single v (1 : k))
    have he : b.coeff.mapDomain q = Finsupp.single v (1 : k) := congrArg MonoidAlgebra.coeff hb
    have hm : v ∈ (b.coeff.mapDomain q).support := by simp [he]
    obtain ⟨z, _, hz⟩ := Finset.mem_image.mp (Finsupp.mapDomain_support hm)
    exact ⟨z, hz⟩
  obtain ⟨χH, _, hχH, _, _⟩ := splitCompositionPairing (k := k) r
  obtain ⟨χT, _, hχT, _, _⟩ := splitCompositionPairing (k := k) n
  intro χ
  obtain ⟨v, hv⟩ := χH.surjective (jH.hom ≫ χ)
  obtain ⟨w, hw⟩ := hqsurj v
  refine ⟨jT.inv ≫ χT w, ?_⟩
  apply (cancel_epi jH.hom).mp
  calc
    jH.hom ≫ i ≫ jT.inv ≫ χT w = (jH.hom ≫ i ≫ jT.inv) ≫ χT w := by
      simp only [Category.assoc]
    _ = χH v := by
      rw [← hq, hχH, hχT, ← specGroupMap_comp]
      congr 1
      apply CommHopfAlgCat.hom_ext
      change (MonoidAlgebra.mapDomainBialgHom k q).comp
        (MonoidAlgebra.mapDomainBialgHom k ((zpowersHom _ w).comp MulEquiv.ulift.toMonoidHom)) =
        MonoidAlgebra.mapDomainBialgHom k ((zpowersHom _ v).comp MulEquiv.ulift.toMonoidHom)
      rw [← MonoidAlgebra.mapDomainBialgHom_comp]
      congr 1
      apply MonoidHom.ext
      intro a
      change q (w ^ a.down.toAdd) = v ^ a.down.toAdd
      rw [map_zpow, hw]
    _ = _ := hv

private def splitCharacterCoordinates {k : Type u} [Field k] {H : GroupScheme k} {r : ℕ}
    (h : IsSplitOfRank H r) : (Fin r → ℤ) ≃ₗ[ℤ] Additive (Character H) := by
  let i := Classical.choice h
  let e := Classical.choice (standardSplitTorus (k := k) r)
  let χ := Classical.choose (splitCompositionPairing (k := k) r)
  exact (latticeCoordinates.{u} r).symm.trans
    (χ.trans (charactersOfIso (e ≪≫ i.symm))).toAdditive.toIntLinearEquiv

open private det_exceptionalCartan_6 det_exceptionalCartan_7
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.ExceptionalStableAlcoveRepresentatives

private theorem exceptionalCartan_det_ne_zero {n : ℕ} (hn : n = 6 ∨ n = 7) :
    (Specs.ExceptionalAffineRootSystems.exceptionalCartan n).det ≠ 0 := by
  rcases hn with rfl | rfl <;> simp [det_exceptionalCartan_6, det_exceptionalCartan_7]

open Specs.ExceptionalAffineRootSystems (exceptionalCartan)

private def numberedRootMap (b : Fin n ≃ D.base.support) : (Fin n → ℤ) →ₗ[ℤ] D.X :=
  (Pi.basisFun ℤ (Fin n)).constr ℤ (fun i => D.datum.root (b i))

private theorem numberedRootMap_rational_surjective (b : Fin n ≃ D.base.support)
    (hb : ExceptionalNumbering D n b) (hn : n = 6 ∨ n = 7) :
    Function.Surjective ((numberedRootMap b).baseChange ℚ) := by
  let _ := D.freeX
  let _ := D.freeY
  let _ := D.finiteX
  let _ := D.finiteY
  let eval : D.X →ₗ[ℤ] (Fin n → ℤ) := LinearMap.pi fun j =>
    D.datum.toLinearMap.flip (D.datum.coroot (b j))
  have hm : eval.comp (numberedRootMap b) = (exceptionalCartan n).transpose.mulVecLin := by
    apply (Pi.basisFun ℤ (Fin n)).ext
    intro i
    change eval ((numberedRootMap b) ((Pi.basisFun ℤ (Fin n)) i)) = _
    rw [numberedRootMap, Module.Basis.constr_basis, Pi.basisFun_apply]
    ext j
    change D.datum.toLinearMap (D.datum.root (b i)) (D.datum.coroot (b j)) =
      ((exceptionalCartan n).transpose.mulVec (Pi.single i 1)) j
    rw [RootPairing.root_coroot_eq_pairing, Matrix.mulVec_single_one]
    exact hb.2 i j
  have hdet : (exceptionalCartan n).transpose.det ≠ 0 := by
    rw [Matrix.det_transpose]
    exact exceptionalCartan_det_ne_zero hn
  have hI : Function.Injective (numberedRootMap b) := by
    intro x y h
    apply Matrix.mulVec_injective_of_det_ne_zero hdet
    change ((exceptionalCartan n).transpose.mulVecLin) x =
      ((exceptionalCartan n).transpose.mulVecLin) y
    rw [← hm]
    exact congrArg eval h
  have hr : Module.finrank ℚ (ℚ ⊗[ℤ] (Fin n → ℤ)) =
      Module.finrank ℚ (ℚ ⊗[ℤ] D.X) := by
    rw [Module.finrank_baseChange, Module.finrank_baseChange,
      Module.finrank_of_isPerfPair D.datum.toLinearMap, hb.1]
    simp
  exact (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hr).mp
    (Module.Flat.lTensor_preserves_injective_linearMap _ hI)

private def restrictCharacterLinear {k : Type u} [Field k] {H T : GroupScheme k} (s : H ⟶ T) :
    Additive (Character T) →ₗ[ℤ] Additive (Character H) :=
  (show Character T →* Character H from
    { toFun := (s ≫ ·)
      map_one' := Grp.hom_ext _ _ (MonObj.comp_one _)
      map_mul' := fun _ _ => Grp.hom_ext _ _ (MonObj.comp_mul _ _ _) }).toAdditive.toIntLinearMap

private theorem integralMap_injective_of_rational_surjective {X : Type*} [AddCommGroup X]
    [Module.Free ℤ X] [Module.Finite ℤ X] {r : ℕ}
    (f : (Fin r → ℤ) →ₗ[ℤ] X) (e : (Fin r → ℤ) ≃ₗ[ℤ] X)
    (hf : Function.Surjective (f.baseChange ℚ)) : Function.Injective f := by
  have hdim : Module.finrank ℚ (ℚ ⊗[ℤ] (Fin r → ℤ)) = Module.finrank ℚ (ℚ ⊗[ℤ] X) := by
    rw [Module.finrank_baseChange, Module.finrank_baseChange]
    exact e.finrank_eq
  have hinj := (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).mpr hf
  intro x y hxy
  have h : (1 : ℚ) ⊗ₜ[ℤ] x = (1 : ℚ) ⊗ₜ[ℤ] y := by
    apply hinj
    simp only [LinearMap.baseChange_tmul, hxy]
  funext i
  have h' := congrArg (fun v => ((Pi.basisFun ℤ (Fin r)).baseChange ℚ).repr v i) h
  have hh : (x i : ℚ) = (y i : ℚ) := by
    simpa only [Module.Basis.baseChange_repr_tmul, zsmul_eq_mul, mul_one, Pi.basisFun_repr] using h'
  exact_mod_cast hh

private theorem surjective_of_factorization {R V W X Y : Type*} [Semiring R]
    [AddCommMonoid V] [AddCommMonoid W] [AddCommMonoid X] [AddCommMonoid Y]
    [Module R V] [Module R W] [Module R X] [Module R Y]
    (a : V →ₗ[R] W) (f : W →ₗ[R] X) (e : X →ₗ[R] Y) (g : V →ₗ[R] Y)
    (h : e.comp (f.comp a) = g) (he : Function.Injective e) (hg : Function.Surjective g) :
    Function.Surjective f := by
  intro x
  obtain ⟨v, hv⟩ := hg (e x)
  refine ⟨a v, he ?_⟩
  exact (congrFun (congrArg DFunLike.coe h) v).trans hv

private theorem rationallySurjective_of_factorization {D₁ D₂ D₃ X Y : Type*}
    [AddCommGroup D₁] [AddCommGroup D₂] [AddCommGroup D₃] [AddCommGroup X] [AddCommGroup Y]
    (a : D₁ →ₗ[ℤ] D₂) (f : D₂ →ₗ[ℤ] X) (e : X →ₗ[ℤ] Y)
    (b : D₁ →ₗ[ℤ] D₃) (g : D₃ →ₗ[ℤ] Y)
    (h : e.comp (f.comp a) = g.comp b)
    (he : Function.Injective e) (hg : Function.Surjective g)
    (hb : Function.Surjective (b.baseChange ℚ)) : Function.Surjective (f.baseChange ℚ) := by
  have h' := congrArg (fun m : D₁ →ₗ[ℤ] Y => m.baseChange ℚ) h
  simp only [LinearMap.baseChange_comp] at h'
  refine surjective_of_factorization _ _ _ _ h'
    (Module.Flat.lTensor_preserves_injective_linearMap e he) ?_
  exact (LinearMap.baseChange_surjective ℚ hg).comp hb

set_option maxHeartbeats 1000000 in
private theorem chart_rootCoordinates {k : Type u} [Field k] {H : AffineAlgebraicGroup k}
    {D : BasedRootDatum.{u}} {M : Model D} {C : MarkedFibre M (SeparableClosure k)}
    (A : AdaptedBorel H C) (b : Fin n ≃ D.base.support)
    (hb : ExceptionalNumbering D n b) (hn : n = 6 ∨ n = 7) (hr : IsSplitOfRank A.S.group r)
    (project : (Fin n → ℤ) →ₗ[ℤ] (Fin r → ℤ))
    (χ : Fin r → Character A.S.group)
    (hχ : ∀ i, A.extendCharacter
      ((Pi.basisFun ℤ (Fin r)).constr ℤ (fun j => Additive.ofMul (χ j))
        (project (Pi.single i 1))).toMul = A.restrictSimple (b i)) :
    HasRootCoordinates A b project := by
  let L := SeparableClosure k
  let B := groupBaseChange k L
  let s := B.map A.intoTorus ≫ A.torus.hom
  let P := C.realization.pinned.pair
  let _ := C.realization.attached.comm
  let e := extendCharacterHom A.S.group A.multiplicative
  let eAdd := e.toAdditive.toIntLinearMap
  let m := (Pi.basisFun ℤ (Fin r)).constr ℤ (fun j => Additive.ofMul (χ j))
  let res := (restrictCharacterLinear s).comp C.realization.datumIso.val.weightEquiv.toLinearMap
  have hres : Function.Surjective res := by
    have hclosed : IsClosedImmersion A.intoTorus.hom.hom.left := by
      let _ := A.T.isClosedImmersion
      let _ : IsClosedImmersion (A.intoTorus.hom.hom.left ≫ A.T.inclusion.hom.hom.left) := by
        change IsClosedImmersion (A.intoTorus ≫ A.T.inclusion).hom.hom.left
        rw [A.intoTorus_eq]
        exact A.S.isClosedImmersion
      exact IsClosedImmersion.of_comp_isClosedImmersion _ A.T.inclusion.hom.hom.left
    have hs : IsClosedImmersion s.hom.hom.left := by
      let _ := baseChangeClosedSubgroup k L A.intoTorus hclosed
      let _ : IsIso A.torus.hom.hom.hom.left :=
        inferInstanceAs (IsIso ((Grp.forget (SchemeOver L) ⋙ Over.forget _).map A.torus.hom))
      change IsClosedImmersion ((B.map A.intoTorus).hom.hom.left ≫ A.torus.hom.hom.hom.left)
      infer_instance
    have hS : IsSplitTorus (B.obj A.S.group) := by
      exact (split_baseChange_dimension L (show IsSplitTorus A.S.group from ⟨r, hr⟩)).1
    let h := splitCharacterRestriction hS P.split s hs
    intro c
    obtain ⟨d, hd⟩ := h c.toMul
    obtain ⟨x, hx⟩ := C.realization.datumIso.val.weightEquiv.surjective (Additive.ofMul d)
    refine ⟨x, ?_⟩
    change restrictCharacterLinear s (C.realization.datumIso.val.weightEquiv x) = c
    rw [hx]
    exact congrArg Additive.ofMul hd
  have hcomp : eAdd.comp (m.comp project) = res.comp (numberedRootMap b) := by
    apply (Pi.basisFun ℤ (Fin n)).ext
    intro i
    change eAdd (m (project ((Pi.basisFun ℤ (Fin n)) i))) =
      res (numberedRootMap b ((Pi.basisFun ℤ (Fin n)) i))
    rw [numberedRootMap, Module.Basis.constr_basis, Pi.basisFun_apply]
    change Additive.ofMul (A.extendCharacter (m (project (Pi.single i 1))).toMul) =
      Additive.ofMul (s ≫ markedCharacter C (b i))
    apply congrArg Additive.ofMul
    exact (hχ i).trans (by
      change s ≫ (C.realization.simpleRoot (b i)).val.val = s ≫ markedCharacter C (b i)
      rw [markedCharacter_eq_simple])
  have hinj : Function.Injective eAdd := by
    intro x y heq
    exact Additive.toMul.injective (extendCharacterHom_injective A.S.group A.multiplicative
      (congrArg Additive.toMul heq))
  have hsurj : Function.Surjective (m.baseChange ℚ) :=
    rationallySurjective_of_factorization project m eAdd (numberedRootMap b) res
      hcomp hinj hres (numberedRootMap_rational_surjective b hb hn)
  let eS := splitCharacterCoordinates hr
  let basis := (Pi.basisFun ℤ (Fin r)).map eS
  let _ := Module.Free.of_basis basis
  let _ := Module.Finite.of_basis basis
  have hm := integralMap_injective_of_rational_surjective m eS hsurj
  refine ⟨m.toAddMonoidHom.toMultiplicative, ?_, fun i => (hχ i).symm⟩
  exact fun x y h => Multiplicative.toAdd.injective (hm (Additive.toMul.injective h))

end CharacterLattices


open Specs.ExceptionalInnerIndices (e6Black e7Black)

private def whiteProjection (white : Fin r → Fin n) : (Fin n → ℤ) →ₗ[ℤ] (Fin r → ℤ) :=
  LinearMap.pi fun j => LinearMap.proj (white j)

private theorem whiteProjection_coordinates (white : Fin r → Fin n)
    (hn : n = 6 ∨ n = 7)
    (hproj : ∀ i, (i ∈ black ∧ whiteProjection white (Pi.single i 1) = 0) ∨
      ∃ j, i = white j ∧ whiteProjection white (Pi.single i 1) = Pi.single j 1) :
    InnerCoordinates.{u} n r black (whiteProjection white) := by
  apply innerChart_of_coordinates
  intro k _ H D M C b A hnum hS hblack
  let e := extendCharacterHom A.S.group A.multiplicative
  have he := extendCharacterHom_surjective A.S.group A.multiplicative (⟨r, hS⟩ : IsSplitTorus _)
  choose χ hχ using fun j : Fin r => he (A.restrictSimple (b (white j)))
  apply chart_rootCoordinates A b hnum hn hS (whiteProjection white) χ
  intro i
  rcases hproj i with ⟨hi, hzero⟩ | ⟨j, hi, hcoord⟩
  · rw [hzero, map_zero]
    change e 1 = A.restrictSimple (b i)
    rw [map_one, (hblack i).mp hi]
  · rw [hcoord, ← Pi.basisFun_apply, Module.Basis.constr_basis, hi]
    exact hχ j

private theorem e6WhiteProjection :
    (whiteProjection ![1, 3] : (Fin 6 → ℤ) →ₗ[ℤ] (Fin 2 → ℤ)) = e6InnerProjection := by
  funext x i
  fin_cases i <;> rfl

private theorem e7WhiteProjection :
    (whiteProjection ![0, 2, 3, 5] : (Fin 7 → ℤ) →ₗ[ℤ] (Fin 4 → ℤ)) = e7InnerProjection := by
  funext x i
  fin_cases i <;> rfl

theorem innerCoordinates : InnerStatement.{u} := by
  constructor
  · rw [← e6WhiteProjection]
    refine whiteProjection_coordinates ![1, 3] (Or.inl rfl) ?_
    intro i
    fin_cases i
    · left; exact ⟨by simp [e6Black, e7Black], by decide⟩
    · right; exact ⟨0, by decide, by decide⟩
    · left; exact ⟨by simp [e6Black, e7Black], by decide⟩
    · right; exact ⟨1, by decide, by decide⟩
    · left; exact ⟨by simp [e6Black, e7Black], by decide⟩
    · left; exact ⟨by simp [e6Black, e7Black], by decide⟩
  · rw [← e7WhiteProjection]
    refine whiteProjection_coordinates ![0, 2, 3, 5] (Or.inr rfl) ?_
    intro i
    fin_cases i
    · right; exact ⟨0, by decide, by decide⟩
    · left; exact ⟨by simp [e6Black, e7Black], by decide⟩
    · right; exact ⟨1, by decide, by decide⟩
    · right; exact ⟨2, by decide, by decide⟩
    · left; exact ⟨by simp [e6Black, e7Black], by decide⟩
    · right; exact ⟨3, by decide, by decide⟩
    · left; exact ⟨by simp [e6Black, e7Black], by decide⟩


section OuterDiagram

open Specs.ExceptionalAffineRootSystems (exceptionalCartan e6Partner restrictedRoot)
open Specs.ExceptionalValuedTorusNormalizer (simplePermutationHom)
open Specs.SteinbergPinnedDescent (E6Diagram e6Involution)

private def e6OrbitIndex : Fin 6 → Fin 4 := ![3, 0, 2, 1, 2, 3]

private theorem e6OrbitIndex_eq (i j : Fin 6) :
    e6OrbitIndex i = e6OrbitIndex j ↔ j = i ∨ j = e6Involution i := by
  fin_cases i <;> fin_cases j <;> decide

private theorem e6OrbitIndex_surjective : Function.Surjective e6OrbitIndex := by
  intro j
  refine ⟨(![1, 3, 2, 0] : Fin 4 → Fin 6) j, ?_⟩
  fin_cases j <;> decide

private theorem e6Cartan_eq_mathlib :
    exceptionalCartan 6 = CartanMatrix.E 6 := by
  ext i j
  fin_cases i <;> fin_cases j <;> decide

private theorem numberedE6Permutation (b : Fin 6 ≃ D.base.support)
    (hb : ExceptionalNumbering D 6 b) (a : Aut D) :
    ((b.trans (simplePermutationHom D a)).trans b.symm) = 1 ∨
      ((b.trans (simplePermutationHom D a)).trans b.symm) = e6Involution := by
  let p := (b.trans (simplePermutationHom D a)).trans b.symm
  apply (show E6Diagram from SteinbergPinnedDescent.e6Diagram).1 p
  intro i j
  have hp (k : Fin 6) : b (p k) = simplePermutationHom D a (b k) := b.apply_symm_apply _
  rw [← e6Cartan_eq_mathlib, ← hb.2, ← hb.2, hp, hp]
  exact a.asIso.hom.val.toHom.pairing

private theorem numberedE6Orbits {Γ : Type*} [Group Γ] (b : Fin 6 ≃ D.base.support)
    (hb : ExceptionalNumbering D 6 b) (ρ : Γ →* Aut D)
    (hρ : ∃ (σ : Γ) (i : Fin 6), simplePermutationHom D (ρ σ) (b i) ≠ b i)
    (i j : Fin 6) :
    e6OrbitIndex i = e6OrbitIndex j ↔
      ∃ σ : Γ, simplePermutationHom D (ρ σ) (b i) = b j := by
  let p (σ : Γ) := (b.trans (simplePermutationHom D (ρ σ))).trans b.symm
  have hp (σ : Γ) (k : Fin 6) : b (p σ k) = simplePermutationHom D (ρ σ) (b k) :=
    b.apply_symm_apply _
  obtain ⟨τ, k, hk⟩ := hρ
  have hτ : p τ = e6Involution := by
    refine (numberedE6Permutation b hb (ρ τ)).resolve_left ?_
    intro h
    apply hk
    rw [← hp, show p τ = 1 from h, Equiv.Perm.one_apply]
  rw [e6OrbitIndex_eq]
  constructor
  · rintro (rfl | rfl)
    · exact ⟨1, by rw [map_one, map_one, Equiv.Perm.one_apply]⟩
    · exact ⟨τ, by rw [← hp, hτ]⟩
  · rintro ⟨σ, hσ⟩
    have hh : p σ i = j := b.injective ((hp _ _).trans hσ)
    rcases numberedE6Permutation b hb (ρ σ) with h | h
    · exact Or.inl (hh.symm.trans (congrArg (fun q : Equiv.Perm (Fin 6) => q i) h))
    · exact Or.inr (hh.symm.trans (congrArg (fun q : Equiv.Perm (Fin 6) => q i) h))

private def foldedProjection : (Fin 6 → ℤ) →ₗ[ℤ] (Fin 4 → ℤ) :=
  let p : Fin 6 → (Fin 6 → ℤ) →ₗ[ℤ] ℤ := fun i => LinearMap.proj i
  LinearMap.pi (![p 1, p 3, p 2 + p 4, p 0 + p 5] :
    Fin 4 → (Fin 6 → ℤ) →ₗ[ℤ] ℤ)

private theorem foldedProjection_eq : (⇑foldedProjection) = restrictedRoot := by
  funext x i
  fin_cases i <;> rfl

private theorem foldedProjection_single (i : Fin 6) :
    foldedProjection (Pi.single i 1) = Pi.single (e6OrbitIndex i) 1 := by
  fin_cases i <;> decide

private theorem coordinates_of_orbit_restrictions {k : Type u} [Field k] {G : AffineAlgebraicGroup k}
    {D : BasedRootDatum.{u}} {M : Model D} {C : MarkedFibre M (SeparableClosure k)}
    (A : AdaptedBorel G C) (b : Fin 6 ≃ D.base.support)
    (hb : ExceptionalNumbering D 6 b) (hS : IsSplitOfRank A.S.group 4)
    (h : ∀ i j, e6OrbitIndex i = e6OrbitIndex j →
      A.restrictSimple (b i) = A.restrictSimple (b j)) :
    HasRootCoordinates A b restrictedRoot := by
  let e := extendCharacterHom A.S.group A.multiplicative
  choose lift hlift using e6OrbitIndex_surjective
  have he := extendCharacterHom_surjective A.S.group A.multiplicative
    (⟨4, hS⟩ : IsSplitTorus _)
  choose χ hχ using fun j : Fin 4 => he (A.restrictSimple (b (lift j)))
  rw [← foldedProjection_eq]
  apply chart_rootCoordinates A b hb (Or.inl rfl) hS foldedProjection χ
  intro i
  rw [foldedProjection_single, ← Pi.basisFun_apply, Module.Basis.constr_basis]
  exact (hχ _).trans (h _ _ (hlift _))

open private det_exceptionalCartan_6
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.ExceptionalStableAlcoveRepresentatives

set_option maxHeartbeats 550000 in
/-- The determinant-three Cartan matrix leaves no integral form of the
E₆ root datum between the simply connected and adjoint lattices. -/
private theorem e6_lattice_alternatives (b : Fin 6 ≃ D.base.support)
    (hb : ExceptionalNumbering D 6 b) :
    D.datum.corootSpan ℤ = ⊤ ∨ D.datum.rootSpan ℤ = ⊤ := by
  classical
  let _ := D.freeX
  let _ := D.freeY
  let _ := D.finiteX
  let _ := D.finiteY
  let by' := (Module.finBasis ℤ D.Y).reindex (finCongr hb.1)
  let p : D.X ≃ₗ[ℤ] Module.Dual ℤ D.Y := D.datum.toLinearMap.toPerfPair
  let bx := by'.dualBasis.map p.symm
  let b₀ := Pi.basisFun ℤ (Fin 6)
  let x := numberedRootMap b
  let y := b₀.constr ℤ (fun i => D.datum.coroot (b i))
  let X := LinearMap.toMatrix b₀ bx x
  let Y := LinearMap.toMatrix b₀ by' y
  let e : D.X →ₗ[ℤ] (Fin 6 → ℤ) := LinearMap.pi (fun j =>
    D.datum.toLinearMap.flip (D.datum.coroot (b j)))
  have he : LinearMap.toMatrix bx b₀ e = Y.transpose := by
    ext i j
    rw [LinearMap.toMatrix_apply, Matrix.transpose_apply]
    change (b₀.repr (e (bx j))) i = LinearMap.toMatrix b₀ by' y j i
    rw [LinearMap.toMatrix_apply]
    change (p (bx j)) (D.datum.coroot (b i)) = by'.repr (y (b₀ i)) j
    have hbx : bx j = p.symm (by'.dualBasis j) := Module.Basis.map_apply _ _ _
    rw [hbx, LinearEquiv.apply_symm_apply, Module.Basis.dualBasis_apply]
    rw [show y (b₀ i) = D.datum.coroot (b i) from Module.Basis.constr_basis _ _ _ _]
  have hC : LinearMap.toMatrix b₀ b₀ (e.comp x) = (exceptionalCartan 6).transpose := by
    ext i j
    rw [LinearMap.toMatrix_apply]
    change D.datum.toLinearMap (x (b₀ j)) (D.datum.coroot (b i)) = exceptionalCartan 6 j i
    rw [show x (b₀ j) = D.datum.root (b j) from Module.Basis.constr_basis _ _ _ _,
      RootPairing.root_coroot_eq_pairing]
    exact hb.2 j i
  rw [LinearMap.toMatrix_comp b₀ bx b₀, he] at hC
  have hdet : (3 : ℤ) = Y.det * X.det := by
    have h := congrArg Matrix.det hC
    rw [Matrix.det_mul, Matrix.det_transpose, Matrix.det_transpose,
      det_exceptionalCartan_6] at h
    exact h.symm
  have hMatrix {W : Type u} [AddCommGroup W] [Module ℤ W] (bw : Module.Basis (Fin 6) ℤ W)
      (f : (Fin 6 → ℤ) →ₗ[ℤ] W)
      (hf : IsUnit (LinearMap.toMatrix b₀ bw f).det) : Function.Surjective f := by
    intro z
    let A := LinearMap.toMatrix b₀ bw f
    obtain ⟨v, hv⟩ := (Matrix.mulVec_surjective_iff_isUnit.mpr
      ((Matrix.isUnit_iff_isUnit_det A).mpr hf)) (bw.equivFun z)
    refine ⟨v, bw.equivFun.injective ?_⟩
    change (fun i => bw.repr (f v) i) = (fun i => bw.repr z i)
    rw [← LinearMap.toMatrix_mulVec_repr b₀ bw f v]
    exact hv
  rcases Int.prime_three.irreducible.isUnit_or_isUnit hdet with hy | hx
  · left
    have h : LinearMap.range y = ⊤ := LinearMap.range_eq_top.mpr (hMatrix by' y hy)
    apply top_unique
    rw [← h]
    change LinearMap.range (b₀.constr ℤ (fun i => D.datum.coroot (b i))) ≤
      Submodule.span ℤ (Set.range D.datum.coroot)
    rw [Module.Basis.constr_range]
    exact Submodule.span_mono (by rintro _ ⟨i, rfl⟩; exact ⟨(b i).val, rfl⟩)
  · right
    have h : LinearMap.range x = ⊤ := LinearMap.range_eq_top.mpr (hMatrix bx x hx)
    apply top_unique
    rw [← h]
    change LinearMap.range (b₀.constr ℤ (fun i => D.datum.root (b i))) ≤
      Submodule.span ℤ (Set.range D.datum.root)
    rw [Module.Basis.constr_range]
    exact Submodule.span_mono (by rintro _ ⟨i, rfl⟩; exact ⟨(b i).val, rfl⟩)

end OuterDiagram

section OuterTorus

open Opposite
open Specs.ExceptionalAffineBruhat (RamifiedReference)
open Specs.AdjointCocharacters (coordinateHopfIso)
open Specs.GeometricBorelConjugacy (subgroupOfSubgroup)
open Specs.ExceptionalLocalRootCoordinates (simpleCorootBasis fundamentalCoweightBasis)
open Specs.ExceptionalValuedTorusNormalizer (OrbitIndices orbitIndex markedDiagramEquiv simplePermutationHom)
open Specs.Unipotent (closedSubgroupAlgebraicGroup)
open Specs.DiagonalizableGroups (groupAlgebra)
open Specs.CharacterDescent (StandardLattice)
open LinearAlgebraicGroups.Arithmetic.ExceptionalValuedTorusNormalizer
  (markedPinnedTorus largestSplitPermutationSubtorus borelSplitTorusCentralizer
    centralizingSplitTorusNormalizer)
open _root_.LinearAlgebraicGroups.CharacterDescent (standardSplitTorus)
open private latticeCoordinates from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.RootData.CharacterPairing

private theorem e6_orbit_equivalence {k E : Type u} [Field k] [Field E] [Algebra k E]
    (b : Fin 6 ≃ D.base.support) (hb : ExceptionalNumbering D 6 b)
    (ρ : Gal(E/k) →* Aut D)
    (hρ : ∃ (σ : Gal(E/k)) (i : Fin 6), simplePermutationHom D (ρ σ) (b i) ≠ b i) :
    let r := (simplePermutationHom D).comp ρ
    ∃ e : OrbitIndices r ≃ Fin 4, ∀ i, e (orbitIndex r (b i)) = e6OrbitIndex i := by
  intro r
  letI : MulAction Gal(E/k) D.base.support := MulAction.compHom _ r
  have hf (i j : D.base.support) :
      e6OrbitIndex (b.symm i) = e6OrbitIndex (b.symm j) ↔
        ∃ σ : Gal(E/k), r σ i = j := by
    change _ ↔ ∃ σ : Gal(E/k), simplePermutationHom D (ρ σ) i = j
    simpa only [Equiv.apply_symm_apply] using numberedE6Orbits b hb ρ hρ (b.symm i) (b.symm j)
  let f : OrbitIndices r → Fin 4 := Quotient.lift (fun i => e6OrbitIndex (b.symm i)) (by
    intro i j h
    exact ((hf j i).mpr h).symm)
  have hfi : Function.Injective f := by
    intro i j
    induction i using Quotient.inductionOn with
    | _ i =>
      induction j using Quotient.inductionOn with
      | _ j =>
        intro h
        apply Quotient.sound
        exact (hf j i).mp h.symm
  have hfs : Function.Surjective f := by
    intro j
    obtain ⟨i, hi⟩ := e6OrbitIndex_surjective j
    exact ⟨orbitIndex r (b i), by change e6OrbitIndex (b.symm (b i)) = j; rw [b.symm_apply_apply, hi]⟩
  refine ⟨Equiv.ofBijective f ⟨hfi, hfs⟩, ?_⟩
  intro i
  change e6OrbitIndex (b.symm (b i)) = e6OrbitIndex i
  rw [b.symm_apply_apply]

private theorem splitGroupAlgebra_rank_four {k : Type u} [Field k] {O : Type u} (e : O ≃ Fin 4) :
    IsSplitOfRank (specGroup (groupAlgebra k (Multiplicative (O →₀ ℤ)))) 4 := by
  letI : Finite O := Finite.of_equiv _ e.symm
  let i : (O →₀ ℤ) ≃ₗ[ℤ] (Fin 4 → ℤ) :=
    (Finsupp.linearEquivFunOnFinite ℤ ℤ O).trans (LinearEquiv.piCongrLeft' ℤ (fun _ : O => ℤ) e)
  let j : Multiplicative (O →₀ ℤ) ≃* StandardLattice.{u} 4 :=
    (i.trans (latticeCoordinates.{u} 4).symm).toAddEquiv.toMultiplicative
  obtain ⟨d⟩ := standardSplitTorus (k := k) 4
  let g := CommHopfAlgCat.isoMk (MonoidAlgebra.domCongrBialgEquiv k k j.symm)
  exact ⟨(hopfSpec (CommRingCat.of k)).mapIso g.op ≪≫ d⟩

set_option maxHeartbeats 700000 in
private theorem outerReferenceSplitTorus {k E : Type u} [Field k] [Field E] [Algebra k E]
    [FiniteDimensional k E] [IsGalois k E]
    (R : RamifiedReference k E M) (b : Fin 6 ≃ D.base.support) (hb : ExceptionalNumbering D 6 b)
    (hd : ∃ (σ : Gal(E/k)) (i : Fin 6), simplePermutationHom D
      (markedDiagramEquiv R.fibre.realization (R.outer σ)) (b i) ≠ b i) :
    ∃ S : ClosedSubgroup R.descent.group.val,
      IsMaximalSplitTorus S ∧ IsSplitOfRank S.group 4 ∧ IsSubgroupOf S R.descent.torus := by
  let _ := D.finiteRoots
  let ρ := (markedDiagramEquiv R.fibre.realization).toMonoidHom.comp R.descent.data.outer
  let r := (simplePermutationHom D).comp ρ
  have hρ : ∃ (σ : Gal(E/k)) (i : Fin 6), simplePermutationHom D (ρ σ) (b i) ≠ b i := by
    simpa only [ρ, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, R.descent.outer_eq] using hd
  obtain ⟨e, _⟩ := e6_orbit_equivalence b hb ρ hρ
  obtain ⟨β, hβ⟩ : ∃ β : Module.Basis D.base.support ℤ D.Y,
      (∃ h, β = simpleCorootBasis D h) ∨ (∃ h, β = fundamentalCoweightBasis D h) := by
    rcases e6_lattice_alternatives b hb with h | h
    · exact ⟨simpleCorootBasis D h, Or.inl ⟨h, rfl⟩⟩
    · exact ⟨fundamentalCoweightBasis D h, Or.inr ⟨h, rfl⟩⟩
  obtain ⟨c, _, hc, _⟩ := markedPinnedTorus D R.fibre.realization R.sequence R.descent.data β hβ
  obtain ⟨q, h, hs, hST, hmax, _⟩ := largestSplitPermutationSubtorus R.descent.torus c hc
  let H := closedSubgroupAlgebraicGroup R.descent.torus
  let S := subgroupOfSubgroup R.descent.torus ⟨_, specGroupMap q ≫ (coordinateHopfIso H).hom, h⟩
  have hTB : IsSubgroupOf R.descent.torus R.descent.borel := ⟨R.descent.inclusion, R.descent.inclusion_comm⟩
  have hZ := borelSplitTorusCentralizer R.descent.group R.descent.reductive R.descent.borel
    R.descent.torus S R.descent.isKBorel R.descent.isTorus R.descent.isMaximal hTB hST hmax
  have hM := (centralizingSplitTorusNormalizer R.descent.group R.descent.torus S hs hST hZ hmax).1
  exact ⟨S, hM, splitGroupAlgebra_rank_four e, hST⟩

end OuterTorus

section OuterAssembly

open Specs.ExceptionalAffineBruhat (RamifiedReference)
open Specs.ExceptionalValuedTorusNormalizer (markedDiagramEquiv simplePermutationHom)
open Specs.GeometricBorelConjugacy (IsKBorel)
open Specs.GeometricRadicals (IsReductive IsTorus)
open Specs.RankOneFlag (IsGeometricallyMaximal)
open Specs.Unipotent (baseChangedAlgebraicGroup closedSubgroupAlgebraicGroup)
open ExceptionalAdaptedPinnedOuterComparison (pinnedOuterComparison)
open ExceptionalAdaptedRationalOppositePair (rationalOppositePair)
open QuasiSplitFixedWeyl (borelIsMinimalParabolic)
open private transportSubgroup from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Reductive.RadicalBaseChange
open private extendSubgroup subgroup_descend subgroup_extend
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.RootData.BorelNormalizer
open private reductive_of_groupIso from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.RootData.RankOneFlag
open private borel_of_square from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Descent.PinnedPairDescent
open private maximal_of_square from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Reductive.MaximalToriConjugate
open private torus_baseChange_algClosure from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Reductive.SubtorusCentralizer

private theorem transport_maximalSplit {k : Type u} [Field k] {X Y : GroupScheme k}
    (f : X ≅ Y) (S : ClosedSubgroup X) (hS : IsMaximalSplitTorus S) :
    IsMaximalSplitTorus (transportSubgroup f S) := by
  refine ⟨hS.1, ?_⟩
  intro U hU ⟨i, hi⟩
  let V := transportSubgroup f.symm U
  have hSV : IsSubgroupOf S V := by
    refine ⟨i, ?_⟩
    change i ≫ U.inclusion ≫ f.inv = S.inclusion
    change i ≫ U.inclusion = S.inclusion ≫ f.hom at hi
    rw [← Category.assoc, hi, Category.assoc, f.hom_inv_id, Category.comp_id]
  obtain ⟨j, hj⟩ := hS.2 V hU hSV
  refine ⟨j, ?_⟩
  change j ≫ S.inclusion ≫ f.hom = U.inclusion
  change j ≫ S.inclusion = U.inclusion ≫ f.inv at hj
  rw [← Category.assoc, hj, Category.assoc, f.inv_hom_id, Category.comp_id]

private theorem transport_borel {k : Type u} [Field k] {X Y : AffineAlgebraicGroup k}
    (f : X.val ≅ Y.val) (B : ClosedSubgroup X.val) (h : IsKBorel B) :
    IsKBorel (transportSubgroup f B) := by
  let L := AlgebraicClosure k
  let B' := transportSubgroup f B
  let U := groupBaseChange k L
  refine ⟨(extendSubgroup L B').isClosedImmersion, ?_⟩
  apply borel_of_square (X := baseChangedAlgebraicGroup L X) (Y := baseChangedAlgebraicGroup L Y)
    (U.mapIso f) (extendSubgroup L B) (extendSubgroup L B') (Iso.refl _)
  · rw [Iso.refl_hom, Category.id_comp]
    exact U.map_comp B.inclusion f.hom
  · exact h.choose_spec

private theorem transport_geometricMaximal {k : Type u} [Field k] {X Y : GroupScheme k}
    (f : X ≅ Y) (T : ClosedSubgroup X) (h : IsGeometricallyMaximal T) :
    IsGeometricallyMaximal (transportSubgroup f T) := by
  let L := AlgebraicClosure k
  let T' := transportSubgroup f T
  refine ⟨(extendSubgroup L T').isClosedImmersion, ?_⟩
  have hT : IsMaximalTorus (extendSubgroup L T) := h.choose_spec
  apply maximal_of_square ((groupBaseChange k L).mapIso f) (extendSubgroup L T)
    (extendSubgroup L T') (Iso.refl _) _ hT
  rw [Iso.refl_hom, Category.id_comp]
  exact (groupBaseChange k L).map_comp T.inclusion f.hom

private theorem maximal_of_geometric {k : Type u} [Field k] {G : AffineAlgebraicGroup k}
    (T : ClosedSubgroup G.val) (ht : IsTorus T.group) (hm : IsGeometricallyMaximal T) :
    IsMaximalTorus T := by
  refine ⟨ht, ?_⟩
  intro U hU hTU
  let L := AlgebraicClosure k
  have h : IsMaximalTorus (extendSubgroup L T) := hm.choose_spec
  exact subgroup_descend L (h.2 (extendSubgroup L U)
    (torus_baseChange_algClosure (closedSubgroupAlgebraicGroup U) hU) (subgroup_extend L hTU))

private theorem transport_comparison_square {k L : Type u} [Field k] [Field L] [Algebra k L]
    {X Y : GroupScheme k} (f : X ≅ Y) (T : ClosedSubgroup X)
    {P Q : GroupScheme L} (i : P ⟶ Q) (e : Q ≅ (groupBaseChange k L).obj X)
    (t : P ≅ (groupBaseChange k L).obj T.group)
    (h : i ≫ e.hom = t.hom ≫ (groupBaseChange k L).map T.inclusion) :
    i ≫ (e ≪≫ (groupBaseChange k L).mapIso f).hom =
      t.hom ≫ (groupBaseChange k L).map (transportSubgroup f T).inclusion := by
  let U := groupBaseChange k L
  change i ≫ e.hom ≫ U.map f.hom = t.hom ≫ U.map (T.inclusion ≫ f.hom)
  rw [← Category.assoc, h, U.map_comp, Category.assoc]

private theorem equalSubgroupIso_inclusion {k : Type u} [Field k] {X : GroupScheme k}
    {U V : ClosedSubgroup X} (h : U = V) :
    (eqToIso (congrArg (fun (W : ClosedSubgroup X) => W.group) h)).hom ≫ V.inclusion = U.inclusion := by
  subst V
  simp

set_option maxHeartbeats 750000 in
theorem outerCoordinates : OuterStatement.{u} := by
  intro k K _ _ _ _ _ _ _ _ G D M R b hb hd f
  obtain ⟨S₀, hS₀, hr, s, hs⟩ := outerReferenceSplitTorus R b hb hd
  let S := transportSubgroup f S₀
  let T := transportSubgroup f R.descent.torus
  let J := transportSubgroup f R.descent.borel
  have hG : IsReductive G := reductive_of_groupIso f R.descent.reductive
  have hJ : IsKBorel J := transport_borel f R.descent.borel R.descent.isKBorel
  have hTm : IsGeometricallyMaximal T :=
    transport_geometricMaximal f R.descent.torus R.descent.isMaximal
  have hT : IsTorus T.group := R.descent.isTorus
  have hTJ : R.descent.inclusion ≫ J.inclusion = T.inclusion := by
    change R.descent.inclusion ≫ R.descent.borel.inclusion ≫ f.hom =
      R.descent.torus.inclusion ≫ f.hom
    rw [← Category.assoc, R.descent.inclusion_comm]
  have hST : s ≫ T.inclusion = S.inclusion := by
    change s ≫ R.descent.torus.inclusion ≫ f.hom = S₀.inclusion ≫ f.hom
    rw [← Category.assoc, hs]
  obtain ⟨O, hOpos, hOtor⟩ := rationalOppositePair G hG J T hJ hT hTm ⟨_, hTJ⟩
  have hS : IsMaximalSplitTorus S := transport_maximalSplit f S₀ hS₀
  have hRank : relativeRank G = 4 := by
    obtain ⟨d⟩ := hr
    exact ((Descent.RelativeRank.maximalSplitDimension G hG).2 S hS).symm.trans
      ((dimension_of_iso d).trans (standard_torus_dimension 4))
  obtain ⟨e, hcmp⟩ := pinnedOuterComparison k K R S₀ hS₀.1 s hs
  refine ⟨e, ?_⟩
  let L := SeparableClosure k
  let : Algebra K L := e.toRingHom.toAlgebra
  obtain ⟨C, a, t, v, j, jT, jB, ha, hj, ht, hv, haction, _, _, _, _, hTgeom, hBgeom, hroots⟩ :=
    hcmp
  let U := groupBaseChange k L
  let E := groupBaseChange K L
  let Q := R.fibre.realization.pinned.pair
  let P := C.realization.pinned.pair
  let dG := descentComparison Q.G R.descent.group t R.descent.data.groupIso
  let dT := descentComparison (closedSubgroupAlgebraicGroup Q.T)
    (closedSubgroupAlgebraicGroup R.descent.torus) t R.descent.data.torusIso
  let dB := descentComparison (closedSubgroupAlgebraicGroup Q.B)
    (closedSubgroupAlgebraicGroup R.descent.borel) t R.descent.data.borelIso
  let φ := j ≪≫ (a.app Q.G.val).symm ≪≫ E.mapIso dG ≪≫ a.app R.descent.group.val
  let τ := jT ≪≫ (a.app Q.T.group).symm ≪≫ E.mapIso dT ≪≫ a.app R.descent.torus.group
  let β := jB ≪≫ (a.app Q.B.group).symm ≪≫ E.mapIso dB ≪≫ a.app R.descent.borel.group
  let ambient := φ ≪≫ U.mapIso f
  have hτ : P.T.inclusion ≫ ambient.hom = τ.hom ≫ U.map T.inclusion :=
    transport_comparison_square f R.descent.torus P.T.inclusion φ τ hTgeom
  have hβ : P.B.inclusion ≫ ambient.hom = β.hom ≫ U.map J.inclusion :=
    transport_comparison_square f R.descent.borel P.B.inclusion φ β hBgeom
  have hTor : τ.inv ≫ P.T.inclusion ≫ ambient.hom = U.map T.inclusion := by
    rw [hτ, Iso.inv_hom_id_assoc]
  let A : AdaptedBorel G C :=
    { S := S
      T := T
      J := J
      maximalSplit := hS
      maximalTorus := maximal_of_geometric T hT hTm
      minimalParabolic := borelIsMinimalParabolic G hG J hJ
      intoTorus := s
      intoTorus_eq := hST
      intoParabolic := R.descent.inclusion
      intoParabolic_eq := hTJ
      ambient := ambient
      torus := τ.symm
      torus_eq := hTor
      borel := β.hom
      borel_eq := hβ.symm
      multiplicative := v
      multiplicative_eq := hv }
  let fB : R.descent.borel.group ≅ O.positive.group :=
    eqToIso (congrArg (fun H => H.group) hOpos.symm)
  let fT : R.descent.torus.group ≅ O.torus.group :=
    eqToIso (congrArg (fun H => H.group) hOtor.symm)
  have hOppB : fB.hom ≫ O.positive.inclusion = R.descent.borel.inclusion ≫ f.hom :=
    equalSubgroupIso_inclusion hOpos.symm
  have hOppT : fT.hom ≫ O.torus.inclusion = R.descent.torus.inclusion ≫ f.hom :=
    equalSubgroupIso_inclusion hOtor.symm
  refine ⟨C, A, O, a, j, t, fB, fT, ha, hj, ht, haction, ?_, hOpos, hOtor,
    hOppB, hOppT, hr, hRank, ?_⟩
  · change (φ ≪≫ U.mapIso f) = _
    simp only [φ, dG, E, U, Q, L, Iso.trans_assoc]
  · apply coordinates_of_orbit_restrictions A b hb hr
    intro i l hil
    let ρ := (markedDiagramEquiv R.fibre.realization).toMonoidHom.comp R.descent.data.outer
    have hρ : ∃ (σ : Gal(K/k)) (i : Fin 6),
        simplePermutationHom D (ρ σ) (b i) ≠ b i := by
      simpa only [ρ, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, R.descent.outer_eq] using hd
    obtain ⟨σ, hσ⟩ := (numberedE6Orbits b hb ρ hρ i l).mp hil
    exact hroots (b i) (b l) σ hσ

end OuterAssembly

end

end LinearAlgebraicGroups.Arithmetic.ExceptionalAdaptedRootCoordinates
