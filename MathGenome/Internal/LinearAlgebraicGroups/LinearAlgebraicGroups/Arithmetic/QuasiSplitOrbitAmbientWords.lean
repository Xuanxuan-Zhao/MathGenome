import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Arithmetic.QuasiSplitOrbitAmbientWords
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.RootData.OrderedRootProducts
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.RootData.DatumAndWeyl
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.UnitaryRankOne
import Batteries.Tactic.OpenPrivate

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj BigOperators

universe u

namespace LinearAlgebraicGroups.Arithmetic.QuasiSplitOrbitAmbientWords

open _root_.LinearAlgebraicGroups.Specs (AffineAlgebraicGroup ClosedSubgroup GroupScheme)
open Specs.QuasiSplitOrbitAmbientWords
open Specs.AbstractPairing (Datum Root)
open Specs.BorelsAndChambers (subgroupRoots)
open Specs.GeometricBorelConjugacy (IsKBorel subgroupOfSubgroup)
open Specs.GeometricRadicals (IsReductive IsSplitTorus IsUnipotentRadical)
open Specs.OrderedRootProducts (Enumerates Parametrizes RootSubgroupFamily product rootProduct)
open Specs.RankOneFlag (IsGeometricallyMaximal)
open Specs.SchemeDerivedGroup (IsSubgroupOf)
open Specs.Unipotent (baseChangedAlgebraicGroup closedSubgroupAlgebraicGroup)

open private factor_of_baseChange from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Affine.ClosedSubgroups
open private factor_group_through_subgroup from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Reductive.GeometricBorelConjugacy


noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000
set_option linter.style.haveILetI false

variable {F K : Type u} [Field F] [Field K] [Algebra F K]

private def extendClosed {G : GroupScheme F} (U : ClosedSubgroup G) :
    ClosedSubgroup ((groupBaseChange F K).obj G) :=
  scalarExtendedSubgroup K U
    (LinearAlgebraicGroups.baseChangeClosedSubgroup F K U.inclusion U.isClosedImmersion)

private theorem descendInclusion {G : GroupScheme F} {U V : ClosedSubgroup G}
    (h : IsSubgroupOf (extendClosed (K := K) U) (extendClosed V)) :
    IsSubgroupOf U V := by
  obtain ⟨j, hj⟩ := h
  letI := V.isClosedImmersion
  obtain ⟨b, hb⟩ := factor_of_baseChange K U.inclusion.hom.hom V.inclusion.hom.hom
    j.hom.hom (congrArg (fun f : (extendClosed (K := K) U).group ⟶
      (groupBaseChange F K).obj G ↦ f.hom.hom) hj)
  exact factor_group_through_subgroup V U.inclusion b hb

variable {k : Type u} [Field k]

private def productIdentity {G : AffineAlgebraicGroup k} {T : ClosedSubgroup G.val}
    (U : RootSubgroupFamily T) (Y : SchemeOver k) :
    (l : List (Root T)) → Y ⟶ product (fun a => (U a).val.group.X) l
  | [] => toUnit Y
  | _ :: l => lift 1 (productIdentity U Y l)

private theorem productIdentity_comp {G : AffineAlgebraicGroup k} {T : ClosedSubgroup G.val}
    (U : RootSubgroupFamily T) (Y : SchemeOver k) (l : List (Root T)) :
    productIdentity U Y l ≫ rootProduct U l = 1 := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    simp only [productIdentity, rootProduct, MonObj.comp_mul, lift_fst_assoc, lift_snd_assoc,
      MonObj.one_comp, ih, mul_one]

private theorem existsEnumeration {I : Type u} [Finite I] (S : Set I) :
    ∃ l : List I, Enumerates l S := by
  classical
  let t := (Set.toFinite S).toFinset
  exact ⟨t.toList, Finset.nodup_toList _, by simp [t]⟩

private theorem enumerateWithFirst {I : Type u} [Finite I] {S : Set I} {a : I} (ha : a ∈ S) :
    ∃ l : List I, Enumerates (a :: l) S := by
  classical
  obtain ⟨l, h₁, h₂⟩ := existsEnumeration (S \ {a})
  refine ⟨l, List.nodup_cons.mpr ⟨fun h ↦ (h₂ a).mp h |>.2 rfl, h₁⟩, ?_⟩
  intro b
  rw [List.mem_cons, h₂]
  by_cases h : b = a
  · subst b
    simp [ha]
  · simp [h]

private theorem radicalProduct {G : AffineAlgebraicGroup k} {T : ClosedSubgroup G.val}
    (hG : IsReductive G) (hT : IsSplitTorus T.group) (hmax : IsGeometricallyMaximal T)
    (B : BorelRadical G) (hTB : IsSubgroupOf T B.borel) (U : RootSubgroupFamily T)
    (l : List (Root T)) (hl : Enumerates l (subgroupRoots T B.borel)) :
    Parametrizes U l B.inAmbient.inclusion.hom.hom := by
  obtain ⟨R, hR, hp⟩ := LinearAlgebraicGroups.RootData.OrderedRootProducts.borelRadicalProduct
    G hG T hT hmax B.borel B.isBorel hTB
  obtain ⟨e, he, _⟩ := LinearAlgebraicGroups.GeometricRadicals.radicalUnique
    (closedSubgroupAlgebraicGroup B.borel) Specs.Unipotent.IsUnipotent hR B.isRadical
  obtain ⟨p, hp⟩ := hp U l hl
  refine ⟨p ≪≫ (Grp.forget (SchemeOver k)).mapIso e, ?_⟩
  have H : e.hom.hom.hom ≫ B.radical.inclusion.hom.hom = R.inclusion.hom.hom :=
    congrArg (fun f : R.group ⟶ B.borel.group ↦ f.hom.hom) he
  change p.hom ≫ e.hom.hom.hom ≫
    B.radical.inclusion.hom.hom ≫ B.borel.inclusion.hom.hom = _
  rw [← Category.assoc e.hom.hom.hom, H]
  exact hp

private theorem rootInRadical {G : AffineAlgebraicGroup k} {T : ClosedSubgroup G.val}
    [Finite (Root T)] (hG : IsReductive G) (hT : IsSplitTorus T.group)
    (hmax : IsGeometricallyMaximal T) (B : BorelRadical G) (hTB : IsSubgroupOf T B.borel)
    (U : RootSubgroupFamily T) (a : Root T) (ha : a ∈ subgroupRoots T B.borel) :
    IsSubgroupOf (U a).val B.inAmbient := by
  obtain ⟨l, hl⟩ := enumerateWithFirst ha
  obtain ⟨p, hp⟩ := radicalProduct hG hT hmax B hTB U (a :: l) hl
  let j := lift (𝟙 (U a).val.group.X) (productIdentity U (U a).val.group.X l)
  apply factor_group_through_subgroup B.inAmbient (U a).val.inclusion (j ≫ p.hom)
  rw [Category.assoc, hp]
  simp only [j, rootProduct, MonObj.comp_mul, lift_fst_assoc, lift_snd_assoc, Category.id_comp,
    productIdentity_comp, mul_one]

private theorem productFactors {G : AffineAlgebraicGroup k} {T : ClosedSubgroup G.val}
    (U : RootSubgroupFamily T) {H J : GroupScheme k} (g : G.val ⟶ H) (j : J ⟶ H) :
    ∀ l : List (Root T),
      (∀ a ∈ l, ∃ f : (U a).val.group ⟶ J, f ≫ j = (U a).val.inclusion ≫ g) →
      ∃ f : product (fun a => (U a).val.group.X) l ⟶ J.X,
        f ≫ j.hom.hom = rootProduct U l ≫ g.hom.hom
  | [], _ => ⟨1, by simp [rootProduct, MonObj.one_comp]⟩
  | a :: l, h => by
    obtain ⟨f, hf⟩ := h a List.mem_cons_self
    obtain ⟨p, hp⟩ := productFactors U g j l (fun b hb ↦ h b (List.mem_cons_of_mem _ hb))
    refine ⟨(fst _ _ ≫ f.hom.hom) * (snd _ _ ≫ p), ?_⟩
    have hff : f.hom.hom ≫ j.hom.hom = (U a).val.inclusion.hom.hom ≫ g.hom.hom :=
      congrArg (fun v : (U a).val.group ⟶ H ↦ v.hom.hom) hf
    simp only [rootProduct, MonObj.mul_comp, Category.assoc, hff, hp]

private def SplitRadical.asBorelRadical {G : AffineAlgebraicGroup F} {B : BorelRadical G}
    (A : SplitRadical K B) : BorelRadical (baseChangedAlgebraicGroup K G) :=
  ⟨A.borel, A.isBorel, A.radical, A.isRadical⟩

private theorem splitRadicalInclusion {O : OrbitLevi F} (A : SplitOrbit O K) (s : Bool) :
    IsSubgroupOf (extendClosed (K := K) (O.derivedRadical s)) (extendClosed (O.radical s)) := by
  let H := baseChangedAlgebraicGroup K O.derivedGroup
  let T := A.T
  let S := A.S
  let U := SplitRadical.asBorelRadical (A.ambient s)
  let V := SplitRadical.asBorelRadical (A.derived s)
  letI : IsCommMonObj T.group.X := A.comm
  letI : Finite (Root A.T) := A.D.finiteRoots
  letI : Finite (Root A.S) := Finite.of_equiv _ A.rootIndex.symm
  let g := (groupBaseChange F K).map O.inclusion
  obtain ⟨l, hl⟩ := existsEnumeration (subgroupRoots S V.borel)
  obtain ⟨e, he⟩ := radicalProduct (G := H) A.hReductive A.sSplit A.sMax V
    (A.sInBorel s) A.derivedRootGroups l hl
  obtain ⟨p, hp⟩ := productFactors A.derivedRootGroups g U.inAmbient.inclusion l (by
    intro i hi
    obtain ⟨e, he⟩ := A.rootMatch i
    obtain ⟨f, hf⟩ := rootInRadical A.reductive A.tSplit A.tMax U
      (A.tInBorel s) A.rootGroups (A.rootIndex i).val ((A.rootSigns s i).mp (hl.2 i |>.mp hi))
    exact ⟨e.hom ≫ f, by rw [Category.assoc, hf, he]⟩)
  apply factor_group_through_subgroup (extendClosed (K := K) (O.radical s)) _ (e.inv ≫ p)
  have hU : U.inAmbient.inclusion = (extendClosed (K := K) (O.radical s)).inclusion := by
    change (groupBaseChange F K).map (O.B s).radical.inclusion ≫
      (groupBaseChange F K).map (O.B s).borel.inclusion = _
    rw [← Functor.map_comp]
    rfl
  have hV : V.inAmbient.inclusion ≫ g = (extendClosed (K := K) (O.derivedRadical s)).inclusion := by
    change ((groupBaseChange F K).map (O.Hpair s).radical.inclusion ≫
      (groupBaseChange F K).map (O.Hpair s).borel.inclusion) ≫
      (groupBaseChange F K).map O.inclusion = _
    rw [← Functor.map_comp, ← Functor.map_comp]
    rfl
  rw [← hU, Category.assoc, hp, ← he, Category.assoc e.hom, Iso.inv_hom_id_assoc, ← hV]
  rfl

theorem radicalInclusions : RadicalInclusions.{u} := by
  intro F K _ _ _ O A s
  exact descendInclusion (splitRadicalInclusion A s)

section RationalWords

open Specs.UnitaryRankOne
open LinearAlgebraicGroups.Arithmetic.UnitaryRankOne
  (admissibleCoordinates splitRankOneWords unitaryTorusAndWeylWords)

private theorem radicalPoint_mem {O : OrbitLevi F} (A : SplitOrbit O K) (s : Bool)
    {x : RationalPoints O.H}
    (hx : x ∈ (onRational (O.Hpair s).inAmbient.inclusion).range) :
    onRational O.inclusion x ∈ O.generated := by
  obtain ⟨y, rfl⟩ := hx
  obtain ⟨f, hf⟩ := radicalInclusions O A s
  apply Subgroup.subset_closure
  refine ⟨s, onRational f y, ?_⟩
  change (y ≫ f.hom.hom) ≫ (O.radical s).inclusion.hom.hom =
    (y ≫ (O.Hpair s).inAmbient.inclusion.hom.hom) ≫ O.inclusion.hom.hom
  rw [Category.assoc, ← Grp.comp_hom_hom, hf]
  simp only [Category.assoc, Grp.comp_hom_hom]
  rfl

private theorem generatedPoint_mem {O : OrbitLevi F} (A : SplitOrbit O K)
    {x : RationalPoints O.H} (hx : x ∈ O.derivedGenerated) :
    onRational O.inclusion x ∈ O.generated := by
  have h : O.derivedGenerated ≤ O.generated.comap (onRational O.inclusion) :=
    (Subgroup.closure_le _).mpr (by
      rintro y ⟨s, hy⟩
      exact radicalPoint_mem A s hy)
  exact h hx

private theorem torusPoint_eq (O : OrbitLevi F) (t : RationalPoints O.S.group) :
    onRational (O.torusMap ≫ O.T.inclusion) t =
      onRational O.inclusion (onRational O.S.inclusion t) := by
  change t ≫ (O.torusMap ≫ O.T.inclusion).hom.hom =
    (t ≫ O.S.inclusion.hom.hom) ≫ O.inclusion.hom.hom
  rw [Grp.comp_hom_hom, Category.assoc, O.intersection.w]

private theorem torusWordImage {O : OrbitLevi F} (A : SplitOrbit O K)
    (t : RationalPoints O.S.group) (ht : onRational O.S.inclusion t ∈ O.derivedGenerated) :
    onRational (O.torusMap ≫ O.T.inclusion) t ∈ O.generated := by
  rw [torusPoint_eq]
  exact generatedPoint_mem A ht

private theorem orthogonalRationalWords {E : Type u} [Field E] [Algebra F E]
    {O : OrbitLevi F} {A : SplitOrbit O K} (M : OrthogonalModel A E) :
    (∀ t : RationalPoints O.S.group, onRational O.S.inclusion t ∈ O.derivedGenerated) ∧
    M.ground.symm (splitWord 1) ∈ O.derivedGenerated := by
  let f := M.ground.symm.toMonoidHom
  have hu (a : E) : f (splitUpper a) ∈ O.derivedGenerated :=
    Subgroup.subset_closure ⟨true, M.upper a⟩
  have hl (a : E) : f (splitLower a) ∈ O.derivedGenerated :=
    Subgroup.subset_closure ⟨false, M.lower a⟩
  have hw (t : Eˣ) : f (splitWord t) ∈ O.derivedGenerated := by
    rw [splitWord, map_mul, map_mul]
    exact O.derivedGenerated.mul_mem (O.derivedGenerated.mul_mem (hu _) (hl _)) (hu _)
  refine ⟨?_, hw 1⟩
  intro t
  obtain ⟨s, hs⟩ := M.torus t
  have hg : M.ground (onRational O.S.inclusion t) = splitWord s * splitWord (-1) :=
    Subtype.ext (hs.trans (splitRankOneWords.1 s).2.symm)
  have hh := O.derivedGenerated.mul_mem (hw s) (hw (-1))
  rw [← map_mul, ← hg] at hh
  simpa [f] using hh

private theorem unitaryRationalWords {E : Type u} [Field E] [Algebra F E] [Infinite F]
    [Algebra.IsQuadraticExtension F E] [Algebra.IsSeparable F E]
    {O : OrbitLevi F} {A : SplitOrbit O K} (M : AdjacentModel A E) :
    (∀ t : RationalPoints O.S.group, onRational O.S.inclusion t ∈ O.derivedGenerated) ∧
    ∃ v : M.matrices, v.val.val = unitaryWeyl E ∧
      M.ground.symm v ∈ O.derivedGenerated := by
  let f := M.ground.symm.toMonoidHom
  let σ := quadraticConjugation F E
  let U := unitaryRadicalGenerators σ 1
  let H := (O.derivedGenerated.comap f).map M.matrices.subtype
  obtain ⟨hupper, hlower, _, _⟩ := admissibleCoordinates (F := F) (E := E) (1 : Fˣ)
  simp only [Units.val_one, map_one] at hupper hlower
  have hU : Subgroup.closure U ≤ H := by
    apply (Subgroup.closure_le H).mpr
    intro x hx
    obtain ⟨a, b, hab, h | h⟩ := hx
    · have hm : x ∈ M.matrices := (M.isUnitary x).mpr (by
        rw [h, upper]
        exact (hupper _ _ _).mpr ⟨rfl, hab⟩)
      exact ⟨⟨x, hm⟩, Subgroup.subset_closure ⟨true, M.upper _ ⟨a, b, h⟩⟩, rfl⟩
    · have hm : x ∈ M.matrices := (M.isUnitary x).mpr (by
        rw [h, lower]
        exact (hlower _ _ _).mpr ⟨rfl, hab⟩)
      exact ⟨⟨x, hm⟩, Subgroup.subset_closure ⟨false, M.lower _ ⟨a, b, h⟩⟩, rfl⟩
  obtain ⟨hdiag, hwords, hweyl, _⟩ :=
    unitaryTorusAndWeylWords (F := F) (E := E) (1 : Fˣ)
  refine ⟨?_, ?_⟩
  · intro t
    let v := M.ground (onRational O.S.inclusion t)
    obtain ⟨d, hd⟩ := M.torus t
    have hform := (M.isUnitary v.val).mp v.prop
    have hdet := v.val.prop
    change v.val.val = Matrix.diagonal d at hd
    rw [hd] at hform hdet
    obtain ⟨s, hs⟩ := (hdiag d).mp ⟨hdet, by simpa using hform⟩
    obtain ⟨x, hx, hxs⟩ := (hwords s).1
    have hxe : x = v.val := Subtype.ext (hxs.trans (hs.symm.trans hd.symm))
    obtain ⟨y, hy, hyv⟩ := hU (by simpa using hx)
    have he : y = v := Subtype.ext (hyv.trans hxe)
    have hh : f v ∈ O.derivedGenerated := he ▸ hy
    simpa [f, v] using hh
  · obtain ⟨x, hx, hw⟩ := hweyl
    obtain ⟨y, hy, hyv⟩ := hU (by simpa using hx)
    exact ⟨y, (congrArg Subtype.val hyv).trans hw, hy⟩

end RationalWords

section Normalizer

open Specs.UnitaryRankOne
open Specs.RootGroups (rootPoint rankOneWord IsRootSubgroup)
open Specs.CharacterDescent (Character Cocharacter)
open LinearAlgebraicGroups.CocharacterDynamics (cocharacterPoint)
open LinearAlgebraicGroups.Arithmetic.UnitaryRankOne (splitRankOneWords)

open private rationalSectionsEquiv labelConjugation inducedConjugation_unique
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.RootData.DatumAndWeyl
open private cocharacterPoint_postcompose from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.RootData.OrderedRootProducts
open private cocharacterPoint_inv from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.RootData.RootGroups

private def fromSection (G : GroupScheme k) :
    (𝟙_ (SchemeOver k) ⟶ G.X) ≃* RationalPoints G where
  toFun p := (groundPointIso k).inv ≫ p
  invFun p := (groundPointIso k).hom ≫ p
  left_inv p := Iso.hom_inv_id_assoc _ p
  right_inv p := Iso.inv_hom_id_assoc _ p
  map_mul' _ _ := MonObj.comp_mul _ _ _

private theorem fromSection_eq (G : GroupScheme k) (p : 𝟙_ (SchemeOver k) ⟶ G.X) :
    fromSection G p = toUnit _ ≫ p := by
  change (groundPointIso k).inv ≫ p = _
  congr 1
  exact (toUnit_unique _ (groundPointIso k).inv).symm

private theorem extendPoint_natural {G H : GroupScheme F} (f : G ⟶ H) (p : RationalPoints G) :
    extendPoint (K := K) H (onRational f p) =
      onRational ((groupBaseChange F K).map f) (extendPoint (K := K) G p) := by
  change (groundPointIso K).inv ≫ scalarExtendedRationalPoint K
    ((groundPointIso F).hom ≫ (p ≫ f.hom.hom)) =
    ((groundPointIso K).inv ≫ scalarExtendedRationalPoint K
      ((groundPointIso F).hom ≫ p)) ≫ (baseChange F K).map f.hom.hom
  simp only [scalarExtendedRationalPoint, Functor.map_comp, Category.assoc]

private theorem normalizes_of_extended {G : AffineAlgebraicGroup F} (T : ClosedSubgroup G.val)
    (p : RationalPoints G.val)
    (hp : Normalizes ((groupBaseChange F K).map T.inclusion)
      (extendPoint (K := K) G.val p)) :
    Normalizes T.inclusion p := by
  obtain ⟨N, hN⟩ := normalizerScheme F G T
  obtain ⟨hclosed, hNK⟩ := normalizerSchemeBaseChange F K T.inclusion N T.isClosedImmersion hN
  obtain ⟨n, hn⟩ := (hNK _ _).mp hp
  let p₀ := (groundPointIso F).hom ≫ p
  let ε := Functor.LaxMonoidal.ε (baseChange F K)
  let i := N.inclusion.hom.hom
  haveI : IsIso ε := inferInstance
  haveI : IsClosedImmersion i.left := N.isClosedImmersion
  obtain ⟨m, hm⟩ := factor_of_baseChange K p₀ i
    (inv ε ≫ (groundPointIso K).hom ≫ n) (by
      change inv ε ≫ (groundPointIso K).hom ≫ n ≫ (baseChange F K).map i = _
      change n ≫ (baseChange F K).map i =
        (groundPointIso K).inv ≫ ε ≫ (baseChange F K).map p₀ at hn
      rw [hn, Iso.hom_inv_id_assoc, IsIso.inv_hom_id_assoc])
  exact (hN _ _).mpr ⟨(groundPointIso F).inv ≫ m, by
    rw [Category.assoc, hm, Iso.inv_hom_id_assoc]⟩

private def labelPoint {O : OrbitLevi F} (A : SplitOrbit O K) :
    (letI : IsCommMonObj A.T.group.X := A.comm; A.rootDatum.weylGroup) →*
    (letI : IsCommMonObj A.T.group.X := A.comm; RationalPoints A.W.scheme.val) :=
  letI : IsCommMonObj A.T.group.X := A.comm
  (fromSection A.W.scheme.val).toMonoidHom.comp
    (A.W.image.constantGroup.sectionPoint.comp A.W.labelEquiv.toMonoidHom)

private theorem rootSubgroup_le {G : AffineAlgebraicGroup k} {T : ClosedSubgroup G.val}
    (hG : IsReductive G) (hT : IsSplitTorus T.group) (hmax : IsGeometricallyMaximal T)
    {a : Root T} {U V : ClosedSubgroup G.val}
    (hU : IsRootSubgroup T U a.val) (hV : IsRootSubgroup T V a.val) :
    IsSubgroupOf U V := by
  obtain ⟨_, _, _, _, _, h⟩ := (LinearAlgebraicGroups.RootData.RootGroups.rootSubgroups
    G hG T hT hmax).2 a.val a.property |>.2.2
  obtain ⟨p, hp⟩ := (h U hU).2
  obtain ⟨q, hq⟩ := (h V hV).1
  exact ⟨p ≫ q, by rw [Category.assoc, hq, hp]⟩

private theorem exists_noninvolutive_unit (k : Type u) [Field k] [Infinite k] :
    ∃ t : kˣ, (t : k) ≠ (↑t⁻¹ : k) := by
  classical
  let S : Finset k := {0, 1, -1}
  obtain ⟨a, ha⟩ := S.finite_toSet.exists_notMem
  have h0 : a ≠ 0 := fun h => ha (by simp [S, h])
  refine ⟨Units.mk0 a h0, ?_⟩
  intro h
  have ht := Units.mul_inv (Units.mk0 a h0)
  rw [← h] at ht
  have hsq : a ^ 2 = (1 : k) ^ 2 := by simpa [pow_two] using ht
  rcases eq_or_eq_neg_of_sq_eq_sq a 1 hsq with h | h
  · exact ha (by simp [S, h])
  · exact ha (by simp [S, h])

private abbrev splitDiagonal {R : Type u} [CommRing R] (t : Rˣ) : SL₂ R :=
  splitWord t * splitWord (-1)

private theorem antiDiagonal_word {k : Type u} [Field k] {t : kˣ}
    (ht : (t : k) ≠ (↑t⁻¹ : k)) (x : SL₂ k)
    (h : x * splitDiagonal t = splitDiagonal t⁻¹ * x) :
    ∃ a : kˣ, x = splitDiagonal a * splitWord 1 := by
  have hm := congrArg Subtype.val h
  change x.val * (splitDiagonal t).val = (splitDiagonal t⁻¹).val * x.val at hm
  rw [(splitRankOneWords.1 t).2, (splitRankOneWords.1 t⁻¹).2] at hm
  have h00 := congrArg (fun m : Matrix (Fin 2) (Fin 2) k ↦ m 0 0) hm
  have h11 := congrArg (fun m : Matrix (Fin 2) (Fin 2) k ↦ m 1 1) hm
  simp [Matrix.mul_diagonal, Matrix.diagonal_mul, mul_comm] at h00 h11
  have ht' : (t : k) ≠ (t : k)⁻¹ := by simpa using ht
  have hz₀ : x.val 0 0 = 0 := h00.resolve_left ht'
  have hz₁ : x.val 1 1 = 0 := h11.resolve_left ht'.symm
  have hd := x.prop
  rw [Matrix.det_fin_two, hz₀, hz₁, zero_mul, zero_sub] at hd
  have ha : x.val 0 1 ≠ 0 := by
    intro ha
    rw [ha, zero_mul, neg_zero] at hd
    exact zero_ne_one hd
  let a := Units.mk0 (x.val 0 1) ha
  have hb : x.val 1 0 = -(↑a⁻¹ : k) := by
    apply mul_left_cancel₀ ha
    have hh : (a : k) * (↑a⁻¹ : k) = 1 := Units.mul_inv a
    change x.val 0 1 * x.val 1 0 = (a : k) * -(↑a⁻¹ : k)
    rw [mul_neg, hh]
    exact (neg_eq_iff_eq_neg.mp hd)
  have hmat : x = splitWord a := by
    apply Subtype.ext
    rw [(splitRankOneWords.1 a).1]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [hz₀, hz₁, hb, a]
  have hone : splitWord (1 : kˣ) * splitWord (-1) = 1 := by
    apply Subtype.ext
    change (splitDiagonal (1 : kˣ)).val = (1 : Matrix (Fin 2) (Fin 2) k)
    rw [(splitRankOneWords.1 (1 : kˣ)).2]
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  have hcancel : splitWord (-1 : kˣ) * splitWord 1 = 1 :=
    (mul_eq_one_iff_eq_inv.mp hone).symm ▸ mul_inv_cancel (splitWord (-1 : kˣ))
  exact ⟨a, by rw [hmat, mul_assoc, hcancel, mul_one]⟩

set_option maxHeartbeats 1000000 in
/-- Compare the attached simple-reflection word with the matrix block. Its
action inverts the attached coroot, so its preimage in the block is
antidiagonal. Removing the resulting diagonal factor preserves the quotient
label and gives the standard matrix word at 1. -/
private theorem blockRepresentative [Infinite K] {O : OrbitLevi F}
    (A : SplitOrbit O K) (i : A.face)
    (f : SL₂ K →* RationalPoints ((groupBaseChange F K).obj O.G.val))
    (hfinj : Function.Injective f) (hmark : RootBlockMark A i f) :
    letI : IsCommMonObj A.T.group.X := A.comm
    ∃ n : RationalPoints A.W.normalizer.group,
      onRational A.W.normalizer.inclusion n = f (splitWord 1) ∧
      onRational A.W.quotient n = labelPoint A (RootPairing.weylGroup.ofIdx A.rootDatum i.val) := by
  letI : IsCommMonObj A.T.group.X := A.comm
  let P := A.rootDatum
  let W := A.W
  let s := RootPairing.weylGroup.ofIdx P i.val
  let c : Cocharacter A.T.group := Additive.toMul (P.coroot i.val)
  obtain ⟨j, hj, hupper, hlower⟩ := hmark.opposite
  obtain ⟨C, _, _, _, D, E, _, Q, B, a, L, x, y, hx, hy, hr⟩ := A.D.attached i.val
  dsimp only at hr
  obtain ⟨_, _, r, hrc⟩ := hr
  have hx' := rootSubgroup_le A.reductive A.tSplit A.tMax hx (A.rootGroups i.val).property
  have hy' := rootSubgroup_le A.reductive A.tSplit A.tMax
    (show IsRootSubgroup A.T _ j.val from hj ▸ hy) (A.rootGroups j).property
  obtain ⟨u, hu⟩ := hx'
  obtain ⟨v, hv⟩ := hy'
  let R := rationalAlgebra K
  obtain ⟨a₁, ha₁⟩ := hupper
    (onRational u (rootPoint x.root.hom R 1))
  obtain ⟨a₂, ha₂⟩ := hlower
    (onRational v (rootPoint y.root.hom R (-1)))
  have hword : f (splitUpper a₁ * splitLower a₂ * splitUpper a₁) =
      fromSection _ r.representative := by
    rw [fromSection_eq, r.representative_word, map_mul, map_mul, ha₁, ha₂]
    have hupos : u.hom.hom ≫ (A.rootGroups i.val).val.inclusion.hom.hom =
        D.contracting.inclusion.hom.hom ≫ C.subgroup.inclusion.hom.hom :=
      congrArg (fun q : D.contracting.group ⟶ (baseChangedAlgebraicGroup K O.G).val ↦ q.hom.hom) hu
    have hvneg : v.hom.hom ≫ (A.rootGroups j).val.inclusion.hom.hom =
        E.contracting.inclusion.hom.hom ≫ C.subgroup.inclusion.hom.hom :=
      congrArg (fun q : E.contracting.group ⟶ (baseChangedAlgebraicGroup K O.G).val ↦ q.hom.hom) hv
    simp only [rankOneWord, rootPoint, onRational, onPoints]
    change ((rootPoint x.root.hom R 1 ≫ u.hom.hom) ≫ (A.rootGroups i.val).val.inclusion.hom.hom) *
      ((rootPoint y.root.hom R (-1) ≫ v.hom.hom) ≫ (A.rootGroups j).val.inclusion.hom.hom) *
      ((rootPoint x.root.hom R 1 ≫ u.hom.hom) ≫ (A.rootGroups i.val).val.inclusion.hom.hom) = _
    simp only [Category.assoc, hupos, hvneg, rootPoint, Grp.comp_hom_hom,
      Units.val_one, inv_one]
  obtain ⟨p, hp⟩ := (W.representsNormalizer _ _).mp r.normalizes
  obtain ⟨ls, hls⟩ := rationalSectionsEquiv W.image.constantGroup
  obtain ⟨l, hl⟩ := ls.surjective (p ≫ W.quotient.hom.hom)
  have hq : p ≫ W.quotient.hom.hom = W.image.constantGroup.sectionPoint l :=
    hl.symm.trans (hls l)
  have hconj : W.image.conjugation l = r.conjugation :=
    inducedConjugation_unique (G := baseChangedAlgebraicGroup K O.G) (T := A.T)
      (g := r.representative) (hp ▸ labelConjugation W.image l p hq) r.conjugates
  have hlab : l = W.labelEquiv s := by
    apply Subtype.ext
    apply MulEquiv.ext
    intro χ
    rw [W.image.characterAction, hconj, r.reflection]
    apply Additive.ofMul.injective
    rw [← W.characterAction s]
    change Additive.ofMul (χ * i.val.val ^ (-Specs.CharacterPairing.pairing A.T.group χ r.coroot)) =
      (RootPairing.Equiv.reflection P i.val).weightEquiv (Additive.ofMul χ)
    rw [RootPairing.Equiv.reflection_weightEquiv, RootPairing.reflection_apply,
      show P.coroot' i.val (Additive.ofMul χ) =
        Specs.CharacterPairing.pairing A.T.group χ r.coroot from
          hrc.symm ▸ A.D.pairing_eq χ c,
      A.D.root_eq, ofMul_mul, ofMul_zpow, neg_smul, sub_eq_add_neg]
  have hq' : onRational W.quotient (fromSection _ p) = labelPoint A s := by
    change (groundPointIso K).inv ≫ p ≫ W.quotient.hom.hom =
      (groundPointIso K).inv ≫ W.image.constantGroup.sectionPoint (W.labelEquiv s)
    rw [hq, hlab]
  have hinv : c ≫ r.conjugation.hom = c⁻¹ := by
    have hc := W.cocharacterAction s c
    rw [← hlab, hconj] at hc
    change (RootPairing.Equiv.reflection P i.val).coweightEquiv.symm (P.coroot i.val) =
      Additive.ofMul (c ≫ r.conjugation.hom) at hc
    rw [RootPairing.Equiv.reflection_coweightEquiv] at hc
    apply Additive.ofMul.injective
    rw [← hc]
    apply (P.coreflection i.val).injective
    rw [LinearEquiv.apply_symm_apply, ofMul_inv, map_neg]
    exact (neg_neg (P.coroot i.val)).symm.trans
      (congrArg Neg.neg (P.coreflection_apply_self (i := i.val)).symm)
  obtain ⟨t, ht⟩ := exists_noninvolutive_unit K
  let z := splitUpper a₁ * splitLower a₂ * splitUpper a₁
  have hmat : z * splitDiagonal t = splitDiagonal t⁻¹ * z := by
    apply hfinj
    simp only [map_mul, hmark.coroot, show f z = _ from hword]
    have hh := congrArg (fun g : A.T.group.X ⟶ _ ↦ cocharacterPoint c R t ≫ g) r.conjugates
    let x := cocharacterPoint c R t
    let y := cocharacterPoint c R t⁻¹
    let a₀ : RationalPoints (baseChangedAlgebraicGroup K O.G).val := toUnit _ ≫ r.representative
    let j₀ := A.T.inclusion.hom.hom
    let x₀ : RationalPoints (baseChangedAlgebraicGroup K O.G).val := x ≫ j₀
    have htor : x ≫ r.conjugation.hom.hom.hom = y := by
      rw [show x ≫ r.conjugation.hom.hom.hom =
        cocharacterPoint (c ≫ r.conjugation.hom) R t from
          (cocharacterPoint_postcompose c r.conjugation.hom R t).symm, hinv]
      change CocharacterDynamics.unitPoint R t ≫ (c⁻¹).hom.hom = _
      rw [Grp.Hom.hom_hom_inv, GrpObj.comp_inv]
      exact (cocharacterPoint_inv c R t).symm
    have he : cocharacterPoint c R t ≫ toUnit A.T.group.X = toUnit _ := by subsingleton
    have hEq : (x ≫ r.conjugation.hom.hom.hom) ≫ j₀ =
        a₀ * x₀ * a₀⁻¹ := by
      simpa only [Grp.comp_hom_hom, MonObj.comp_mul, GrpObj.comp_inv, ← Category.assoc,
        he, x, a₀, x₀, j₀] using hh
    rw [htor] at hEq
    rw [fromSection_eq]
    exact mul_inv_eq_iff_eq_mul.mp hEq.symm
  obtain ⟨b, hb⟩ := antiDiagonal_word ht z hmat
  let d := onRational W.torusInclusion (cocharacterPoint c R b)
  let n := d⁻¹ * fromSection W.normalizer.group p
  refine ⟨n, ?_, ?_⟩
  · have hd : onRational W.normalizer.inclusion d = f (splitDiagonal b) := by
      change cocharacterPoint c R b ≫ W.torusInclusion.hom.hom ≫
        W.normalizer.inclusion.hom.hom = _
      rw [← Grp.comp_hom_hom, W.inclusion_eq]
      exact (hmark.coroot b).symm
    have hp' : onRational W.normalizer.inclusion (fromSection _ p) = f z := by
      change (groundPointIso K).inv ≫ p ≫ W.normalizer.inclusion.hom.hom = f z
      rw [hp]
      exact hword.symm
    change onRational W.normalizer.inclusion n = _
    rw [show n = d⁻¹ * fromSection W.normalizer.group p from rfl, map_mul, map_inv, hd, hp', hb,
      f.map_mul (splitDiagonal b) (splitWord 1), inv_mul_cancel_left]
  · have hd : onRational W.quotient d = 1 := by
      change (cocharacterPoint c R b ≫ W.torusInclusion.hom.hom) ≫ W.quotient.hom.hom = _
      rw [Category.assoc, W.isQuotient.1.w, ← Category.assoc, comp_toUnit]
      rfl
    change onRational W.quotient n = _
    rw [show n = d⁻¹ * fromSection W.normalizer.group p from rfl, map_mul, map_inv, hd, inv_one, one_mul, hq']

private theorem ambientPoint_injective (O : OrbitLevi F) :
    Function.Injective (onRational ((groupBaseChange F K).map O.inclusion)) := by
  let V := extendClosed (K := K) (subgroupOfSubgroup O.L O.deriv)
  letI : IsClosedImmersion V.inclusion.hom.hom.left := V.isClosedImmersion
  letI : Mono V.inclusion.hom.hom := Over.mono_of_mono_left _
  intro x y h
  exact (cancel_mono V.inclusion.hom.hom).mp h

private theorem normalizes_of_lift {O : OrbitLevi F} (A : SplitOrbit O K)
    (g : RationalPoints O.G.val) :
    (letI : IsCommMonObj A.T.group.X := A.comm
     ∃ n : RationalPoints A.W.normalizer.group,
       onRational A.W.normalizer.inclusion n = extendPoint (K := K) O.G.val g) →
    Normalizes O.T.inclusion g := by
  letI : IsCommMonObj A.T.group.X := A.comm
  rintro ⟨n, hn⟩
  apply normalizes_of_extended (K := K)
  exact (A.W.representsNormalizer _ _).mpr ⟨n, hn⟩

private theorem weightProduct {O : OrbitLevi F} (A : SplitOrbit O K) :
    letI : IsCommMonObj A.T.group.X := A.comm
    ∀ x y : A.rootDatum.weylGroup, ∀ c : Additive (Character A.T.group),
      (x * y).val.weightEquiv c = x.val.weightEquiv (y.val.weightEquiv c) :=
  fun _ _ _ ↦ rfl

private theorem simpleWeight {O : OrbitLevi F} (A : SplitOrbit O K) :
    letI : IsCommMonObj A.T.group.X := A.comm
    ∀ i j : Root A.T,
      (RootPairing.weylGroup.ofIdx A.rootDatum i).val.weightEquiv (A.rootDatum.root j) =
        A.rootDatum.root j - A.rootDatum.pairing j i • A.rootDatum.root i := by
  letI : IsCommMonObj A.T.group.X := A.comm
  intro i j
  exact A.rootDatum.reflection_apply_root (i := i) (j := j)

private theorem longest_of_simple_images {O : OrbitLevi F} (A : SplitOrbit O K) :
    letI : IsCommMonObj A.T.group.X := A.comm
    ∀ w : A.rootDatum.weylGroup,
      w ∈ Specs.StandardParabolicLevi.parabolicWeylGroup A.D A.face →
      (∀ j : A.face, ∃ a : A.face,
        w.val.weightEquiv (A.rootDatum.root j.val) = - A.rootDatum.root a.val) →
      IsFaceLongest A w := by
  classical
  letI : IsCommMonObj A.T.group.X := A.comm
  letI : Finite (Root A.T) := A.D.finiteRoots
  let P := A.rootDatum
  intro w hw hsimple
  refine ⟨hw, ?_⟩
  intro i hi hip
  obtain ⟨a, ha, hsign, hsum⟩ := A.based.integral_coordinates i
  have hp (j : Root A.T) (hj : j ∈ A.base.support) : 0 < A.positive (P.root j) :=
    ((A.based.simple_iff j).mp hj).1
  have han : ∀ j, 0 ≤ a j := by
    rcases hsign with h | h
    · exact h
    · exfalso
      apply (not_lt_of_ge _ hip)
      rw [hsum, map_sum]
      apply Finset.sum_nonpos
      intro j hj
      rw [map_smul, zsmul_eq_mul]
      exact mul_nonpos_of_nonpos_of_nonneg (h j) (hp _ hj).le
  obtain ⟨t, ht, b, hb⟩ := (Submodule.mem_span_image_iff_exists_fun (R := ℤ) (v := P.root)).mp hi
  have htb : t ⊆ A.base.support := fun _ hj ↦ A.isFace (ht hj)
  let b' (j : Root A.T) := if h : j ∈ t then b ⟨j, h⟩ else 0
  have hb' : P.root i = ∑ j ∈ A.base.support, b' j • P.root j := by
    calc
      P.root i = ∑ j : t, b j • P.root j.val := hb.symm
      _ = ∑ j : t, b' j.val • P.root j.val := by
        apply Finset.sum_congr rfl
        intro j _
        simp [b', j.prop]
      _ = ∑ j ∈ t, b' j • P.root j :=
        Finset.sum_coe_sort t (fun j ↦ b' j • P.root j)
      _ = _ := Finset.sum_subset htb (by
        intro j _ hj
        simp [b', hj])
  have hc (j : A.base.support) :
      a j.val = if h : j.val ∈ t then b ⟨j.val, h⟩ else 0 := by
    apply Fintype.linearIndependent_iffₛ.mp A.base.linearIndepOn_root
      (fun j : A.base.support ↦ a j.val) (fun j : A.base.support ↦
        if h : j.val ∈ t then b ⟨j.val, h⟩ else 0) _ j
    calc
      (∑ j : A.base.support, a j.val • P.root j.val) =
          ∑ j ∈ A.base.support, a j • P.root j :=
        Finset.sum_coe_sort A.base.support (fun j ↦ a j • P.root j)
      _ = ∑ j ∈ A.base.support, b' j • P.root j := hsum.symm.trans hb'
      _ = (∑ j : A.base.support, b' j.val • P.root j.val) :=
        (Finset.sum_coe_sort A.base.support (fun j ↦ b' j • P.root j)).symm
  have hnonpos : ∀ j ∈ A.base.support,
      A.positive (w.val.weightEquiv (a j • P.root j)) ≤ 0 := by
    intro j hj
    by_cases h : j ∈ A.face
    · obtain ⟨δ, hδ⟩ := hsimple ⟨j, h⟩
      rw [map_smul, hδ, map_smul, map_neg, zsmul_eq_mul]
      exact mul_nonpos_of_nonneg_of_nonpos (han j) (neg_nonpos.mpr (hp _ (A.isFace δ.prop)).le)
    · have hz : a j = 0 := by
        simpa [show j ∉ t from fun h' ↦ h (ht h')] using hc ⟨j, hj⟩
      simp [hz]
  have hsome : ∃ j ∈ A.base.support, 0 < a j := by
    by_contra! h
    have he : A.positive (P.root i) = 0 := by
      rw [hsum, map_sum, Finset.sum_eq_zero (fun j hj ↦ by
        rw [le_antisymm (h j hj) (han j), zero_smul, map_zero])]
    exact (ne_of_gt hip) he
  obtain ⟨j, hj, haj⟩ := hsome
  have hface : j ∈ A.face := by
    by_contra h
    have hz := hc ⟨j, hj⟩
    simp [show j ∉ t from fun h' ↦ h (ht h')] at hz
    omega
  obtain ⟨d, hd⟩ := hsimple ⟨j, hface⟩
  let eval := A.positive.comp w.val.weightEquiv.toLinearMap
  change eval (P.root i) < 0
  rw [hsum, map_sum eval]
  exact Finset.sum_neg' hnonpos ⟨j, hj, by
    change A.positive (w.val.weightEquiv (a j • P.root j)) < 0
    rw [map_smul, hd, map_smul, map_neg, zsmul_eq_mul]
    exact mul_neg_of_pos_of_neg haj (neg_neg_of_pos (hp _ (A.isFace d.prop)))⟩

private theorem map_splitWord_one {E K : Type u} [Field E] [Field K] (e : E →+* K) :
    Matrix.SpecialLinearGroup.map e (splitWord 1) = splitWord 1 := by
  apply Subtype.ext
  change (splitWord (1 : Eˣ)).val.map e = (splitWord (1 : Kˣ)).val
  rw [(splitRankOneWords.1 (1 : Eˣ)).1, (splitRankOneWords.1 (1 : Kˣ)).1]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

private theorem orthogonalWeight {O : OrbitLevi F} (A : SplitOrbit O K)
    {E : Type u} [Field E] [Algebra F E] (M : OrthogonalModel A E) :
    letI : IsCommMonObj A.T.group.X := A.comm
    letI := Classical.decEq (E →ₐ[F] K)
    ∀ l : List (E →ₐ[F] K), l.Nodup →
      ∀ j : E →ₐ[F] K,
      ((l.map (fun e ↦ RootPairing.weylGroup.ofIdx A.rootDatum (M.indices e).val)).prod).val.weightEquiv
        (A.rootDatum.root (M.indices j).val) =
        if j ∈ l then -A.rootDatum.root (M.indices j).val else A.rootDatum.root (M.indices j).val := by
  classical
  letI : IsCommMonObj A.T.group.X := A.comm
  intro l hd j
  induction l with
  | nil => simp
  | cons i l ih =>
    have ht := List.nodup_cons.mp hd
    simp only [List.map_cons, List.prod_cons, weightProduct A, ih ht.2]
    by_cases hij : j = i
    · subst j
      simp [ht.1, simpleWeight A, RootPairing.pairing_same, two_smul]
    · have hx := M.pairings (M.indices j) (M.indices i)
        (fun h ↦ hij (M.indices.injective h))
      have hs :
          (RootPairing.weylGroup.ofIdx A.rootDatum (M.indices i).val).val.weightEquiv
            (A.rootDatum.root (M.indices j).val) = A.rootDatum.root (M.indices j).val := by
        rw [simpleWeight A, hx, zero_smul, sub_zero]
      by_cases h : j ∈ l
      · simp only [List.mem_cons, hij, false_or, h, ite_true]
        let e := (RootPairing.weylGroup.ofIdx A.rootDatum (M.indices i).val).val.weightEquiv.toLinearMap
        change e (-A.rootDatum.root (M.indices j).val) = -A.rootDatum.root (M.indices j).val
        rw [map_neg e]
        exact congrArg Neg.neg hs
      · simp only [List.mem_cons, hij, false_or, h, ite_false, hs]

private theorem orthogonalMatrixProduct {I : Type u} (l : List I) (hd : l.Nodup)
    (j : I) :
    letI := Classical.decEq I
    ((l.map (fun i ↦ orthogonalBlock K I i (splitWord 1))).prod) j =
      if j ∈ l then splitWord 1 else 1 := by
  classical
  induction l with
  | nil => simp
  | cons i l ih =>
    have ht := List.nodup_cons.mp hd
    simp only [List.map_cons, List.prod_cons, Pi.mul_apply, ih ht.2]
    by_cases hj : j = i
    · subst j
      simp [orthogonalBlock, ht.1]
    · simp [orthogonalBlock, hj]

private theorem adjacentBlock_injective (i : Fin 2) :
    Function.Injective (adjacentBlock K i) := by
  intro a b h
  have hm := congrArg Subtype.val h
  apply Subtype.ext
  ext x y
  fin_cases i <;> fin_cases x <;> fin_cases y <;>
    first
    | simpa [adjacentBlock] using congrArg (fun m : Matrix (Fin 3) (Fin 3) K ↦ m 0 0) hm
    | simpa [adjacentBlock] using congrArg (fun m : Matrix (Fin 3) (Fin 3) K ↦ m 0 1) hm
    | simpa [adjacentBlock] using congrArg (fun m : Matrix (Fin 3) (Fin 3) K ↦ m 1 0) hm
    | simpa [adjacentBlock] using congrArg (fun m : Matrix (Fin 3) (Fin 3) K ↦ m 1 1) hm
    | simpa [adjacentBlock] using congrArg (fun m : Matrix (Fin 3) (Fin 3) K ↦ m 1 2) hm
    | simpa [adjacentBlock] using congrArg (fun m : Matrix (Fin 3) (Fin 3) K ↦ m 2 1) hm
    | simpa [adjacentBlock] using congrArg (fun m : Matrix (Fin 3) (Fin 3) K ↦ m 2 2) hm

private theorem adjacentMatrixProduct :
    (adjacentBlock K 0 (splitWord 1) * adjacentBlock K 1 (splitWord 1) *
      adjacentBlock K 0 (splitWord 1)).val = unitaryWeyl K := by
  change (adjacentBlock K 0 (splitWord 1)).val * (adjacentBlock K 1 (splitWord 1)).val *
    (adjacentBlock K 0 (splitWord 1)).val = _
  simp only [adjacentBlock, MonoidHom.coe_mk, OneHom.coe_mk,
    show (1 : Fin 2) ≠ 0 by decide, ite_false, (splitRankOneWords.1 (1 : Kˣ)).1]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [unitaryWeyl, Matrix.mul_apply, Fin.sum_univ_three]

private theorem adjacentWeight {O : OrbitLevi F} (A : SplitOrbit O K) {E : Type u}
    [Field E] [Algebra F E] [Algebra.IsQuadraticExtension F E] [Algebra.IsSeparable F E]
    (M : AdjacentModel A E) :
    letI : IsCommMonObj A.T.group.X := A.comm
    let s := fun i ↦ RootPairing.weylGroup.ofIdx A.rootDatum (M.indices i).val
    ∀ i : Fin 2, (s 0 * s 1 * s 0).val.weightEquiv (A.rootDatum.root (M.indices i).val) =
      -A.rootDatum.root (M.indices i.rev).val := by
  letI : IsCommMonObj A.T.group.X := A.comm
  intro s i
  have h01 := M.pairings 0 1 (by decide)
  have h10 := M.pairings 1 0 (by decide)
  let α := A.rootDatum.root (M.indices 0).val
  let β := A.rootDatum.root (M.indices 1).val
  let x := (s 0).val.weightEquiv.toLinearMap
  let y := (s 1).val.weightEquiv.toLinearMap
  have hxx : x α = -α := by
    change (s 0).val.weightEquiv α = -α
    rw [simpleWeight A, RootPairing.pairing_same, two_smul]
    abel
  have hxy : x β = β + α := by
    change (s 0).val.weightEquiv β = β + α
    rw [simpleWeight A, h10, neg_one_zsmul, sub_neg_eq_add]
  have hyx : y α = α + β := by
    change (s 1).val.weightEquiv α = α + β
    rw [simpleWeight A, h01, neg_one_zsmul, sub_neg_eq_add]
  have hyy : y β = -β := by
    change (s 1).val.weightEquiv β = -β
    rw [simpleWeight A, RootPairing.pairing_same, two_smul]
    abel
  simp only [weightProduct A]
  fin_cases i
  · change x (y (x α)) = -β
    rw [hxx, map_neg, hyx, map_neg, map_add, hxx, hxy]
    abel
  · change x (y (x β)) = -α
    rw [hxy, map_add, hyy, hyx, map_add, map_neg, hxy, map_add, hxx, hxy]
    abel

private theorem simpleReflection_mem {O : OrbitLevi F} (A : SplitOrbit O K) :
    letI : IsCommMonObj A.T.group.X := A.comm
    ∀ i : A.face, RootPairing.weylGroup.ofIdx A.rootDatum i.val ∈
      Specs.StandardParabolicLevi.parabolicWeylGroup A.D A.face :=
  fun i ↦ Subgroup.subset_closure ⟨i.val, i.prop, rfl⟩

theorem orthogonalWords : OrthogonalWords.{u} := by
  classical
  intro F K E _ _ _ _ _ _ _ _ _ _ O A M
  letI : IsCommMonObj A.T.group.X := A.comm
  haveI : Infinite K := Infinite.of_injective (algebraMap F K) (algebraMap F K).injective
  letI : Finite (Root A.T) := A.D.finiteRoots
  letI : Finite (E →ₐ[F] K) := Finite.of_equiv _ M.indices.symm
  let W := A.W
  let f := onRational ((groupBaseChange F K).map O.inclusion)
  let s (i : E →ₐ[F] K) := RootPairing.weylGroup.ofIdx A.rootDatum (M.indices i).val
  let b (i : E →ₐ[F] K) := orthogonalBlock K (E →ₐ[F] K) i
  have hblock (i : E →ₐ[F] K) :
      ∃ n : RationalPoints W.normalizer.group,
        onRational W.normalizer.inclusion n = f (M.split.symm (b i (splitWord 1))) ∧
        onRational W.quotient n = labelPoint A (s i) := by
    apply blockRepresentative A (M.indices i) (f.comp (M.split.symm.toMonoidHom.comp (b i)))
    · change Function.Injective (f ∘ M.split.symm ∘ b i)
      exact (ambientPoint_injective (K := K) O).comp (M.split.symm.injective.comp
        (by
          intro g h hh
          have he := congrFun hh i
          change Pi.mulSingle (M := fun _ : E →ₐ[F] K ↦ SL₂ K) i g i =
            Pi.mulSingle (M := fun _ : E →ₐ[F] K ↦ SL₂ K) i h i at he
          simpa only [Pi.mulSingle_eq_same] using he))
    · exact M.blocks i
  choose n hn hq using hblock
  obtain ⟨l, hl⟩ := existsEnumeration (Set.univ : Set (E →ₐ[F] K))
  let w := (l.map s).prod
  let m := (l.map n).prod
  let x := M.ground.symm (splitWord 1)
  let g := onRational O.inclusion x
  obtain ⟨ht, hg⟩ := orthogonalRationalWords M
  have hlong : IsFaceLongest A w := by
    apply longest_of_simple_images A w
    · apply Subgroup.list_prod_mem
      intro b hb
      obtain ⟨i, _, rfl⟩ := List.mem_map.mp hb
      exact simpleReflection_mem A (M.indices i)
    · intro i
      let j := M.indices.symm i
      have hj : j ∈ l := (hl.2 j).mpr (Set.mem_univ _)
      have he := orthogonalWeight A M l hl.1 j
      rw [ite_eq_left hj, M.indices.apply_symm_apply] at he
      exact ⟨i, he⟩
  have hmat : (l.map (fun i ↦ b i (splitWord 1))).prod =
      M.split (extendPoint (K := K) O.H x) := by
    funext i
    rw [orthogonalMatrixProduct l hl.1 i, ite_eq_left ((hl.2 i).mpr (Set.mem_univ _)), M.scalar]
    simpa [x] using (map_splitWord_one i.toRingHom).symm
  have hinc : onRational W.normalizer.inclusion m = extendPoint (K := K) O.G.val g := by
    change onRational W.normalizer.inclusion ((l.map n).prod) =
      extendPoint (K := K) O.G.val (onRational O.inclusion x)
    rw [extendPoint_natural, map_list_prod]
    simp only [List.map_map, Function.comp_def, hn]
    let φ := f.comp M.split.symm.toMonoidHom
    have hprod := (map_list_prod φ (l.map (fun i ↦ b i (splitWord 1)))).symm
    simp only [List.map_map, Function.comp_def] at hprod
    calc
      _ = φ ((l.map (fun i ↦ b i (splitWord 1))).prod) := hprod
      _ = _ := by rw [hmat]; simp [φ, f]
  have hlabel : onRational W.quotient m = labelPoint A w := by
    change onRational W.quotient ((l.map n).prod) = labelPoint A ((l.map s).prod)
    simp only [map_list_prod, List.map_map, Function.comp_def, hq]
  exact ⟨radicalInclusions O A, fun t ↦ ⟨ht t, torusWordImage A t (ht t)⟩,
    x, w, m, hg, generatedPoint_mem A hg,
    normalizes_of_lift A g ⟨m, hinc⟩, hlong, hinc, hlabel.trans (fromSection_eq _ _)⟩

theorem adjacentWords : AdjacentWords.{u} := by
  classical
  intro F K E _ _ _ _ _ _ _ _ _ _ O A M
  letI : IsCommMonObj A.T.group.X := A.comm
  haveI : Infinite K := Infinite.of_injective (algebraMap F K) (algebraMap F K).injective
  let W := A.W
  let f := onRational ((groupBaseChange F K).map O.inclusion)
  let s (i : Fin 2) := RootPairing.weylGroup.ofIdx A.rootDatum (M.indices i).val
  let b (i : Fin 2) := adjacentBlock K i
  have hblock (i : Fin 2) :
      ∃ n : RationalPoints W.normalizer.group,
        onRational W.normalizer.inclusion n = f (M.split.symm (b i (splitWord 1))) ∧
        onRational W.quotient n = labelPoint A (s i) := by
    apply blockRepresentative A (M.indices i) (f.comp (M.split.symm.toMonoidHom.comp (b i)))
    · exact (ambientPoint_injective (K := K) O).comp
        (M.split.symm.injective.comp (adjacentBlock_injective i))
    · exact M.blocks i
  choose n hn hq using hblock
  obtain ⟨ht, v, hv, hmem⟩ := unitaryRationalWords M
  let x := M.ground.symm v
  let g := onRational O.inclusion x
  let w := s 0 * s 1 * s 0
  let m := n 0 * n 1 * n 0
  have hlong : IsFaceLongest A w := by
    apply longest_of_simple_images A w
    · let H := Specs.StandardParabolicLevi.parabolicWeylGroup A.D A.face
      exact H.mul_mem (H.mul_mem (simpleReflection_mem A (M.indices 0))
        (simpleReflection_mem A (M.indices 1))) (simpleReflection_mem A (M.indices 0))
    · intro i
      let j := M.indices.symm i
      have he := adjacentWeight A M j
      rw [M.indices.apply_symm_apply] at he
      exact ⟨M.indices j.rev, he⟩
  have hmat : M.split (extendPoint (K := K) O.H x) =
      b 0 (splitWord 1) * b 1 (splitWord 1) * b 0 (splitWord 1) := by
    apply Subtype.ext
    rw [adjacentMatrixProduct, M.scalar]
    have hground : M.ground x = v := M.ground.apply_symm_apply v
    change (M.ground x).val.val.map M.embedding = unitaryWeyl K
    rw [hground, hv]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [unitaryWeyl]
  have hinc : onRational W.normalizer.inclusion m = extendPoint (K := K) O.G.val g := by
    change onRational W.normalizer.inclusion (n 0 * n 1 * n 0) =
      extendPoint (K := K) O.G.val (onRational O.inclusion x)
    simp only [extendPoint_natural, map_mul, hn]
    let φ := f.comp M.split.symm.toMonoidHom
    calc
      _ = φ (b 0 (splitWord 1) * b 1 (splitWord 1) * b 0 (splitWord 1)) := by
        simp only [map_mul, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, φ]
      _ = _ := by rw [← hmat]; simp [φ, f]
  have hlabel : onRational W.quotient m = labelPoint A w := by
    change onRational W.quotient (n 0 * n 1 * n 0) = labelPoint A (s 0 * s 1 * s 0)
    simp only [map_mul, hq]
  exact ⟨radicalInclusions O A, fun t ↦ ⟨ht t, torusWordImage A t (ht t)⟩,
    x, w, m, hmem, generatedPoint_mem A hmem,
    normalizes_of_lift A g ⟨m, hinc⟩, hlong, hinc, hlabel.trans (fromSection_eq _ _)⟩

end Normalizer

end

end LinearAlgebraicGroups.Arithmetic.QuasiSplitOrbitAmbientWords
