import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Arithmetic.ExceptionalValuedScalarTransport
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Affine.GroupSchemes
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.ExceptionalIwahoriCongruence
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.ExceptionalIwahoriImageComparison
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.ExceptionalValuedTorusNormalizer
import Mathlib.AlgebraicGeometry.Sites.Fpqc
import Batteries.Tactic.OpenPrivate

namespace LinearAlgebraicGroups.Arithmetic.ExceptionalValuedScalarTransport

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open Specs.ExceptionalValuedScalarTransport
open scoped CategoryTheory.MonObj
open private whiskerLeft_pullback from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Affine.FixedPointSchemes

universe u
set_option backward.isDefEq.respectTransparency false

/-- A factorization through a monomorphism descends along an fpqc morphism. -/
private theorem factor_of_fpqc {S : Scheme.{u}} {U X Y Z : Over S}
    (p : U ⟶ X) [QuasiCompact p.left] [Surjective p.left] [Flat p.left]
    (i : Y ⟶ Z) [Mono i.left] (g : X ⟶ Z) (b : U ⟶ Y)
    (hb : b ≫ i = p ≫ g) :
    ∃ a, a ≫ i = g := by
  have hb' : b.left ≫ i.left = p.left ≫ g.left := congrArg Over.Hom.left hb
  have hdesc {V : Scheme.{u}} (a a' : V ⟶ U.left) (h : a ≫ p.left = a' ≫ p.left) :
      a ≫ b.left = a' ≫ b.left := by
    apply (cancel_mono i.left).mp
    simp only [Category.assoc, hb', reassoc_of% h]
  let a := EffectiveEpi.desc p.left b.left hdesc
  have ha : a ≫ i.left = g.left := by
    rw [← cancel_epi p.left, ← Category.assoc, EffectiveEpi.fac]
    exact hb'
  refine ⟨Over.homMk a ?_, Over.OverMorphism.ext ha⟩
  rw [← Over.w i, ← Category.assoc, ha, Over.w g]

private theorem specMap_flat_surjective {k k' : Type u} [Field k] [Field k']
    (f : k →+* k') : Flat (Spec.map (CommRingCat.ofHom f)) ∧
      Surjective (Spec.map (CommRingCat.ofHom f)) := by
  let _ : Algebra k k' := f.toAlgebra
  have hf : f.FaithfullyFlat :=
    (RingHom.faithfullyFlat_algebraMap_iff (R := k) (S := k')).mpr inferInstance
  exact (flat_and_surjective_SpecMap_iff (CommRingCat.ofHom f)).mpr hf

private theorem conjugateLe_precomp_iff {F : Type u} [Field F]
    {G H : Specs.GroupScheme F} (i : H ⟶ G) [Mono i.hom.hom.left]
    {U X : SchemeOver F} (p : U ⟶ X)
    [QuasiCompact p.left] [Surjective p.left] [Flat p.left] (g : X ⟶ G.X) :
    ConjugateLe i (p ≫ g) ↔ ConjugateLe i g := by
  let a := H.X ◁ p
  have hpb : IsPullback a.left (snd H.X U).left (snd H.X X).left p.left :=
    (whiskerLeft_pullback (H := H.X) p).map (Over.forget _)
  have : Flat a.left := MorphismProperty.of_isPullback hpb.flip inferInstance
  have : Surjective a.left := MorphismProperty.of_isPullback hpb.flip inferInstance
  have : QuasiCompact a.left := MorphismProperty.of_isPullback hpb.flip inferInstance
  have hc : a ≫ conjugateFamily i g = conjugateFamily i (p ≫ g) := by
    simp only [conjugateFamily, MonObj.comp_mul, GrpObj.comp_inv, a, whiskerLeft_snd_assoc,
      whiskerLeft_fst_assoc]
  constructor
  · rintro ⟨b, hb⟩
    exact factor_of_fpqc a i.hom.hom (conjugateFamily i g) b (hb.trans hc.symm)
  · rintro ⟨b, hb⟩
    exact ⟨a ≫ b, by rw [Category.assoc, hb, hc]⟩

theorem torusConditionsScalar : TorusConditions.{u} := by
  intro F k k' _ _ _ _ _ G T f s x
  let p := (testSpec F).map (CommAlgCat.ofHom f).op
  have : Flat p.left := (specMap_flat_surjective f.toRingHom).1
  have : Surjective p.left := (specMap_flat_surjective f.toRingHom).2
  have : QuasiCompact p.left :=
    inferInstanceAs (QuasiCompact (Spec.map (CommRingCat.ofHom f.toRingHom)))
  have : IsClosedImmersion T.inclusion.hom.hom.left := T.isClosedImmersion
  let y : (testSpec F).obj (Opposite.op (CommAlgCat.of F k)) ⟶ G.X := x
  change (Normalizes T.inclusion (p ≫ y) ↔ Normalizes T.inclusion y) ∧
    (Specs.SchemeDerivedGroup.FactorsThrough T (p ≫ y) ↔
      Specs.SchemeDerivedGroup.FactorsThrough T y)
  constructor
  · simp only [normalizesIff F T.inclusion T.isClosedImmersion, ← GrpObj.comp_inv]
    exact and_congr (conjugateLe_precomp_iff T.inclusion p y)
      (conjugateLe_precomp_iff T.inclusion p y⁻¹)
  · change (∃ b, b ≫ T.inclusion.hom.hom = p ≫ y) ↔
      ∃ a, a ≫ T.inclusion.hom.hom = y
    exact ⟨fun ⟨b, hb⟩ => factor_of_fpqc p T.inclusion.hom.hom y b hb,
      fun ⟨a, ha⟩ => ⟨p ≫ a, by rw [Category.assoc, ha]⟩⟩

section Valued

open Specs.Pinning (BasedRootDatum)
open Specs.IntegralSemisimpleModel
  (Model IntegralPoints integerAlgebra integralSpec TorusValues torusPoint cellMap integralPointFunctor)
open Specs.ExceptionalLocalRootCoordinates (LocalIwahori normalizedValuation)
open Specs.ExceptionalIwahoriCongruence
  (CellValues cellValue cellValuePoint mapCellValues integralRing integralRingMap changeRing changeRingHom)
open Specs.ExceptionalIwahoriImageComparison (MarkedLocalNormalizer integralUnitTorus)
open Specs.ExceptionalMarkedRootDescent (markedWeylWord)
open Specs.ExceptionalValuedTorusNormalizer (FibreNormalizer valuationRingInclusion)
open Specs.OrderedRootProducts (Enumerates)
open ValuativeRel
open private cellValuePoint_bijective iwahoriValuationChart torusPoint_natural
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.ExceptionalIwahoriCongruence
open private rootOrderings_exist from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Classification.IntegralRealization
open private splitMarkedNormalizerWord fibreNormalizerPoint_injective
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.ExceptionalIwahoriImageComparison
open private markedWeylWord_map from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.ExceptionalMarkedRootDescent

attribute [local instance] integerAlgebra

variable {L K : Type u} [Field L] [Field K]
  [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
  [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  {D : BasedRootDatum.{u}} {M : Model D}
  {G H W : Type u} [Group G] [Group H] [Group W]
  {j : G →* IntegralPoints M.group (integralRing L)}
  {j' : H →* IntegralPoints M.group (integralRing K)}

private theorem iwahori_cell (P : LocalIwahori j W)
    (negative positive : List D.I)
    (hn : Enumerates negative {a | ¬D.base.IsPos a})
    (hp : Enumerates positive {a | D.base.IsPos a}) (g : G) :
    g ∈ P.iwahori ↔ ∃ z : CellValues D (integralRing L) negative positive,
      cellValue M.toIntegralMarking (integralRing L) negative positive z = j g ∧
      (∀ χ, normalizedValuation L (z.2.1 χ : L) = 1) ∧
      (∀ l, normalizedValuation L (z.1 l) < 1) ∧
      ∀ l, normalizedValuation L (z.2.2 l) ≤ 1 := by
  let B := P.residueFibre
  let R := IsLocalRing.ResidueField (valuation L).valuationSubring
  obtain ⟨C, hC, hchart⟩ := ExceptionalIwahoriCongruence.markedFibreBorel M.toIntegralMarking R
    B.line B.realization B.groupIso B.torusIso B.coordinate B.torus_comm
    (fun i x => B.root_eval i (CommAlgCat.of R R) x) negative positive hp
  have hB := P.borel_eq.trans hC.symm
  have hRaw := iwahoriValuationChart M.toIntegralMarking j.range (valuation L)
    negative positive hn hp P.residueBorel (hB.trans hchart) ⟨j g, ⟨g, rfl⟩⟩
  change g ∈ P.iwahori ↔ _ at hRaw
  let e := IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt L
  have hOne (x : L) : normalizedValuation L x = 1 ↔ valuation L x = 1 := by
    change e (valuation L x) = 1 ↔ _
    rw [← map_one e]
    exact e.strictMono.injective.eq_iff
  have hLt (x : L) : normalizedValuation L x < 1 ↔ valuation L x < 1 := by
    change e (valuation L x) < 1 ↔ _
    rw [← map_one e, e.strictMono.lt_iff_lt]
  have hLe (x : L) : normalizedValuation L x ≤ 1 ↔ valuation L x ≤ 1 := by
    change e (valuation L x) ≤ 1 ↔ _
    rw [← map_one e, e.strictMono.le_iff_le]
  simp only [hOne, hLt, hLe]
  refine hRaw.trans ⟨ExistsUnique.exists, ?_⟩
  rintro ⟨z, hz⟩
  have hinj := (ExceptionalIwahoriCongruence.markedChart M.toIntegralMarking negative positive hn hp).1
    (integralRing L)
  exact ⟨z, hz, fun w hw => hinj (hw.1.trans hz.1.symm)⟩

private theorem iwahori_scalar (P : LocalIwahori j W) (P' : LocalIwahori j' W)
    (f : L →+* K) (s : G →* H) (hv : ∀ z, normalizedValuation K (f z) = normalizedValuation L z)
    (hs : ∀ g, j' (s g) = changeRingHom M.group (integralRingMap f) (j g)) :
    P'.iwahori.comap s = P.iwahori := by
  obtain ⟨negative, positive, hn, hp⟩ := rootOrderings_exist D
  let i := integralRingMap f
  let c := cellMap M.line M.torus M.root negative positive
  let h := ExceptionalIwahoriCongruence.markedChart M.toIntegralMarking negative positive hn hp
  have hco (z : CellValues D (integralRing L) negative positive) :
      ((∀ χ, normalizedValuation K ((mapCellValues i z).2.1 χ : K) = 1) ∧
        (∀ l, normalizedValuation K ((mapCellValues i z).1 l) < 1) ∧
        ∀ l, normalizedValuation K ((mapCellValues i z).2.2 l) ≤ 1) ↔
      (∀ χ, normalizedValuation L (z.2.1 χ : L) = 1) ∧
        (∀ l, normalizedValuation L (z.1 l) < 1) ∧
        ∀ l, normalizedValuation L (z.2.2 l) ≤ 1 := by
    change ((∀ χ, normalizedValuation K (f (z.2.1 χ : L)) = 1) ∧
      (∀ l, normalizedValuation K (f (z.1 l)) < 1) ∧
      ∀ l, normalizedValuation K (f (z.2.2 l)) ≤ 1) ↔ _
    simp only [hv]
  have : IsOpenImmersion c.left := M.openCell negative positive hn hp
  let p := integralSpec.map i.op
  have : Flat p.left := (specMap_flat_surjective f).1
  have : Surjective p.left := (specMap_flat_surjective f).2
  have : QuasiCompact p.left :=
    inferInstanceAs (QuasiCompact (Spec.map (CommRingCat.ofHom f)))
  ext g
  change s g ∈ P'.iwahori ↔ g ∈ P.iwahori
  rw [iwahori_cell P' negative positive hn hp, iwahori_cell P negative positive hn hp]
  constructor
  · rintro ⟨z', hz', hv'⟩
    have hc : cellValuePoint M.line (integralRing K) negative positive z' ≫ c =
      p ≫ j g := hz'.trans (hs g)
    obtain ⟨b, hb⟩ := factor_of_fpqc p c (j g) _ hc
    obtain ⟨z, rfl⟩ := (cellValuePoint_bijective M.line (integralRing L) negative positive).surjective b
    have hb' : cellValue M.toIntegralMarking (integralRing L) negative positive z = j g := hb
    have he : mapCellValues i z = z' := h.1 _ ((h.2 i z).symm.trans (hb' ▸ (hz'.trans (hs g)).symm))
    exact ⟨z, hb', (hco z).mp (he.symm ▸ hv')⟩
  · rintro ⟨z, hz, hv₀⟩
    exact ⟨mapCellValues i z, (h.2 i z).symm.trans ((congrArg (changeRing i) hz).trans (hs g).symm),
      (hco z).mpr hv₀⟩

private theorem normalizer_torus_word {W : Type u} [Group W]
    (N : MarkedLocalNormalizer L j W) (n : N.normalizer) :
    ∃ t : TorusValues D (integralRing L), j (N.torusPart n) = torusPoint D _ t ≫ M.torus.hom.hom ∧
      j n = (torusPoint D _ t ≫ M.torus.hom.hom : IntegralPoints M.group (integralRing L)) *
        markedWeylWord M.toIntegralMarking (integralRing L) (N.word (N.label n)) := by
  obtain ⟨t, ht⟩ := (N.torusPoints _).mp (N.torusPart n).property
  refine ⟨t, ht, ?_⟩
  rw [← ht, ← N.lift_point, ← map_mul]
  apply congrArg j
  change (n : G) = ((n * (N.lift (N.label n))⁻¹ : N.normalizer) : G) * (N.lift (N.label n) : G)
  simp

/-- Two torus times integral Weyl word expressions of the same split field
point give the same finite label and character logs. -/
private theorem torus_word_comparison
    (l m : List D.I) (hl : ∀ i ∈ l, i ∈ D.base.support)
    (hm : ∀ i ∈ m, i ∈ D.base.support)
    (t v : TorusValues D (integralRing K))
    (he : (torusPoint D _ t ≫ M.torus.hom.hom : IntegralPoints M.group (integralRing K)) *
        markedWeylWord M.toIntegralMarking (integralRing K) l =
      (torusPoint D _ v ≫ M.torus.hom.hom : IntegralPoints M.group (integralRing K)) *
        markedWeylWord M.toIntegralMarking (integralRing K) m) :
    (l.map (RootPairing.weylGroup.ofIdx D.datum)).prod =
      (m.map (RootPairing.weylGroup.ofIdx D.datum)).prod ∧
    ∀ χ : D.X, WithZero.log (normalizedValuation K (t (Multiplicative.ofAdd χ) : K)) =
      WithZero.log (normalizedValuation K (v (Multiplicative.ofAdd χ) : K)) := by
  let _ := D.freeY
  let _ := D.finiteY
  let _ : Fintype (Module.Free.ChooseBasisIndex ℤ D.Y) := Fintype.ofFinite _
  obtain ⟨F⟩ := ExceptionalValuedTorusNormalizer.markedFibreNormalizer K M
  let _ := F.torusComm
  obtain ⟨a, ha, hal⟩ := splitMarkedNormalizerWord F l hl
  obtain ⟨b, hb, hbl⟩ := splitMarkedNormalizerWord F m hm
  obtain ⟨T, ν, _, p, _, _, _, _, _, htor, hlog, _, _, _, _, hind, _⟩ :=
    ExceptionalValuedTorusNormalizer.splitApartmentAction F (Module.Free.chooseBasis ℤ D.Y)
  have hab : (T t).val * a = (T v).val * b := by
    apply fibreNormalizerPoint_injective F
    rw [map_mul, map_mul, htor, htor, ha, hb]
    exact he
  have hlabel (s : TorusValues D (integralRing K)) (c : _) :
      F.label ((T s).val * c) = F.label c := by
    rw [map_mul, MonoidHom.mem_ker.mp (T s).property, one_mul]
  have hintegral (w : List D.I) (c : _) (hc : F.point c =
      markedWeylWord M.toIntegralMarking (integralRing K) w) :
      c ∈ (((integralPointFunctor M.group).map (valuationRingInclusion K)).hom.range).comap F.point := by
    refine ⟨markedWeylWord M.toIntegralMarking _ w, ?_⟩
    rw [hc]
    exact markedWeylWord_map M.toIntegralMarking (valuationRingInclusion K) w
  have hread (s : TorusValues D (integralRing K)) (c : _)
      (hc : c ∈ (((integralPointFunctor M.group).map (valuationRingInclusion K)).hom.range).comap F.point) :
      (p ((T s).val * c)).left = ν s := by
    rw [hind _ c hc (hlabel s c)]
    congr 1
    apply T.injective
    rw [MulEquiv.apply_symm_apply]
    exact Subtype.ext (mul_inv_cancel_right _ _)
  refine ⟨hal.symm.trans ((hlabel t a).symm.trans ((congrArg F.label hab).trans
    ((hlabel v b).trans hbl))), ?_⟩
  have hν : ν t = ν v :=
    (hread t a (hintegral l a ha)).symm.trans
      ((congrArg (fun x => (p x).left) hab).trans (hread v b (hintegral m b hb)))
  intro χ
  exact (hlog t χ).symm.trans
    ((congrArg (fun z => D.datum.toLinearMap χ z.toAdd) hν).trans (hlog v χ))

theorem valuedLocalTransport : ValuedTransport.{u} := by
  classical
  intro L K _ _ _ _ _ _ _ _ D M G H _ _ W _ j j' P P' q hq hword hword' hprod hprod'
    f s hv hs hN _hT N N' U U'
  have hI := iwahori_scalar P P' f s hv hs
  refine ⟨hI, ?_, ?_⟩
  · change ((integralUnitTorus (K := K) M).comap j').comap s =
      (integralUnitTorus (K := L) M).comap j
    rw [← P.intersection, ← P'.intersection]
    change (P'.iwahori ⊓ P'.normalizer.normalizer).comap s = P.iwahori ⊓ P.normalizer.normalizer
    rw [Subgroup.comap_inf, hI, hN]
  · intro n n' hn'
    let i := integralRingMap f
    let l := N.word (N.label n)
    let m := N'.word (N'.label n')
    obtain ⟨t, ht, hn⟩ := normalizer_torus_word N n
    obtain ⟨v, hv', hn''⟩ := normalizer_torus_word N' n'
    let t' : TorusValues D (integralRing K) := (Units.map f).comp t
    have hmap : changeRingHom M.group i
        (torusPoint D _ t ≫ M.torus.hom.hom : IntegralPoints M.group (integralRing L)) =
        (torusPoint D _ t' ≫ M.torus.hom.hom : IntegralPoints M.group (integralRing K)) := by
      change integralSpec.map i.op ≫ torusPoint D _ t ≫ M.torus.hom.hom = _
      rw [← Category.assoc]
      exact congrArg (· ≫ M.torus.hom.hom) (torusPoint_natural i t)
    have hsource : j' n' =
        (torusPoint D _ t' ≫ M.torus.hom.hom : IntegralPoints M.group (integralRing K)) *
          markedWeylWord M.toIntegralMarking (integralRing K) l := by
      rw [hn', hs, hn, map_mul, hmap]
      exact congrArg (_ * ·) (markedWeylWord_map M.toIntegralMarking i l)
    obtain ⟨hlabel, hlog⟩ :=
      torus_word_comparison l m (hword _) (hword' _) t' v (hsource.symm.trans hn'')
    refine ⟨hq ((hprod' _).symm.trans (hlabel.symm.trans (hprod _))), ?_⟩
    apply D.datum.toLinearMap.flip.toPerfPair.injective
    ext χ
    change D.datum.toLinearMap χ (N'.translation (N'.torusPart n')).toAdd =
      D.datum.toLinearMap χ (N.translation (N.torusPart n)).toAdd
    calc
      _ = WithZero.log (normalizedValuation K (v (Multiplicative.ofAdd χ) : K)) :=
        N'.characterLog _ v hv' χ
      _ = WithZero.log (normalizedValuation K (t' (Multiplicative.ofAdd χ) : K)) := (hlog χ).symm
      _ = WithZero.log (normalizedValuation L (t (Multiplicative.ofAdd χ) : L)) :=
        congrArg WithZero.log (hv _)
      _ = _ := (N.characterLog _ t ht χ).symm

end Valued

end LinearAlgebraicGroups.Arithmetic.ExceptionalValuedScalarTransport
