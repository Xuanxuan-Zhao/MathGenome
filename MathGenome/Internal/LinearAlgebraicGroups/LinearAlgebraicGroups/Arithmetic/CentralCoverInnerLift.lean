import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Arithmetic.CentralCoverInnerLift
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Classification.CentralIsogenies
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.RootData.SchemeCentre
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Descent.AutomorphismSequence
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.CategoryTheory.LocallyCartesianClosed.Over
import Batteries.Tactic.OpenPrivate

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

universe u

namespace LinearAlgebraicGroups.Arithmetic.CentralCoverInnerLift

open _root_.LinearAlgebraicGroups.Specs
open Specs.AutomorphismSequence
open Specs.CentralCoverInnerLift
open Specs.CentralIsogenies
open Specs.GeometricRadicals (IsReductive IsSemisimple IsSplitTorus)
open Specs.RankOneFlag (IsGeometricallyMaximal)
open Specs.CharacterPairing (absoluteRoots)
open LinearAlgebraicGroups.Classification.CentralIsogenies
open LinearAlgebraicGroups.Descent.AutomorphismSequence (adjointInner)
open private centralizes_iff from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Affine.Stabilizers
open private schemeKernel_exists schemeKernel_sections from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Affine.SchemeImageQuotient
open private reductive_of_semisimple schemeKernel_eq_iff from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Classification.CentralIsogenies

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

variable {k : Type u} [Field k]

private theorem pullbackSnd_epi {X Y V : SchemeOver k} {f : X ⟶ Y}
    (hf : Flat f.left) (hs : Surjective f.left) (v : V ⟶ Y) :
    Epi (pullback.snd f v) := by
  have h := (Over.forget (Spec (CommRingCat.of k))).map_isPullback
    (IsPullback.of_hasPullback f v)
  let : Flat (pullback.snd f v).left := MorphismProperty.of_isPullback h hf
  let : Surjective (pullback.snd f v).left := MorphismProperty.of_isPullback h hs
  let : Epi (pullback.snd f v).left := Flat.epi_of_flat_of_surjective _
  exact Over.epi_of_epi_left _

private theorem centralizes_image {H G : GroupScheme k} {V : SchemeOver k}
    (q : H ⟶ G) (hf : Flat q.hom.hom.left) (hs : Surjective q.hom.hom.left)
    (z : V ⟶ H.X) (hz : Centralizes (𝟙 H) z) :
    Centralizes (𝟙 G) (z ≫ q.hom.hom) := by
  apply (centralizes_iff _ _).mpr
  intro U t g
  change Commute (t ≫ z ≫ q.hom.hom) g
  let a := pullback.snd q.hom.hom g
  let y := pullback.fst q.hom.hom g
  have : Epi a := pullbackSnd_epi hf hs g
  have hc := (centralizes_iff _ _).mp hz _ (a ≫ t) y
  have h := hc.map (IsMonHom.monoidHom q.hom.hom _)
  change Commute ((a ≫ t ≫ z) ≫ q.hom.hom) (y ≫ q.hom.hom) at h
  have hy : y ≫ q.hom.hom = a ≫ g := pullback.condition
  rw [hy, Category.assoc, Category.assoc] at h
  apply (cancel_epi a).mp
  simpa only [MonObj.comp_mul, Category.assoc] using h.eq

private theorem centralizes_of_cover {H : GroupScheme k} {V X : SchemeOver k}
    {a : V ⟶ X} (hf : Flat a.left) (hs : Surjective a.left)
    {z : X ⟶ H.X} (hz : Centralizes (𝟙 H) (a ≫ z)) :
    Centralizes (𝟙 H) z := by
  apply (centralizes_iff _ _).mpr
  intro U t x
  change Commute (t ≫ z) x
  let b := pullback.snd a t
  let c := pullback.fst a t
  have : Epi b := pullbackSnd_epi hf hs t
  have hc := (centralizes_iff _ _).mp hz _ c (b ≫ x)
  change Commute (c ≫ a ≫ z) (b ≫ x) at hc
  have he : c ≫ a = b ≫ t := pullback.condition
  rw [← Category.assoc, he, Category.assoc] at hc
  apply (cancel_epi b).mp
  simpa only [MonObj.comp_mul, Category.assoc] using hc.eq

private theorem centre_of_torus_lift {H G : AffineAlgebraicGroup k}
    {T : ClosedSubgroup H.val} {S : ClosedSubgroup G.val}
    {qT : T.group ⟶ S.group}
    (hH : IsReductive H) (hG : IsReductive G)
    (hsT : IsSplitTorus T.group) (hmT : IsGeometricallyMaximal T)
    (hsS : IsSplitTorus S.group) (hmS : IsGeometricallyMaximal S)
    (hroots : Set.SurjOn (characterPullback qT) (absoluteRoots S) (absoluteRoots T))
    {V : SchemeOver k} [IsAffine V.left] (t : V ⟶ T.group.X)
    (ht : Centralizes (𝟙 G.val) (t ≫ qT.hom.hom ≫ S.inclusion.hom.hom)) :
    Centralizes (𝟙 H.val) (t ≫ T.inclusion.hom.hom) := by
  obtain ⟨R, ⟨e⟩⟩ := (essImage_algSpec (R := CommRingCat.of k)).mpr
    (show IsAffine V.left from inferInstance)
  obtain ⟨_, _, _, _, _, hT⟩ := RootData.SchemeCentre.schemeCentre H hH T hsT hmT
  obtain ⟨_, _, _, _, _, hS⟩ := RootData.SchemeCentre.schemeCentre G hG S hsS hmS
  have ht' : Centralizes (𝟙 G.val)
      ((e.hom ≫ t ≫ qT.hom.hom) ≫ S.inclusion.hom.hom) := by
    apply (centralizes_iff _ _).mpr
    intro U a x
    simpa only [Category.assoc] using (centralizes_iff _ _).mp ht U (a ≫ e.hom) x
  have h : Centralizes (𝟙 H.val) ((e.hom ≫ t) ≫ T.inclusion.hom.hom) := by
    apply (hT R.unop (e.hom ≫ t)).mpr
    intro α hα
    obtain ⟨β, hβ, rfl⟩ := hroots hα
    change (e.hom ≫ t) ≫ (qT.hom.hom ≫ β.hom.hom) = 1
    simpa only [Category.assoc] using (hS R.unop (e.hom ≫ t ≫ qT.hom.hom)).mp ht' β hβ
  apply (centralizes_iff _ _).mpr
  intro U a x
  simpa only [Category.assoc, Iso.inv_hom_id_assoc] using
    (centralizes_iff _ _).mp h U (a ≫ e.inv) x

private theorem compositeKernel_isCentre {H G : AffineAlgebraicGroup k}
    (hH : IsSemisimple H) (hG : IsSemisimple G)
    {T : ClosedSubgroup H.val} {S : ClosedSubgroup G.val}
    (hsT : IsSplitTorus T.group) (hmT : IsGeometricallyMaximal T)
    (hsS : IsSplitTorus S.group) (hmS : IsGeometricallyMaximal S)
    {q : H.val ⟶ G.val} {qT : T.group ⟶ S.group}
    (hq : IsCentralIsogeny q) (hqT : IsTorusRestriction q qT)
    (Q : AdjointQuotient G) (N : ClosedSubgroup H.val)
    (hN : IsSchemeKernel (q ≫ Q.projection) N) :
    RepresentsSubgroup N (fun _ z ↦ Centralizes (𝟙 H.val) z) := by
  have hrH := reductive_of_semisimple H hH
  have hrG := reductive_of_semisimple G hG
  have centre : Specs.SchemeCentre.CentreFormula.{u} := RootData.SchemeCentre.schemeCentre
  obtain ⟨_, _, hroots, _⟩ := centralIsogenyComparison H G hrH hrG T S
    hsT hmT hsS hmS q qT hq hqT.1 hqT.2.2
  obtain ⟨K, hK, hcentralK⟩ := hq.2.2.2
  have hcentreQ : Centralizes (𝟙 G.val) Q.centre.inclusion.hom.hom :=
    (Q.isCentre _ _).mpr ⟨𝟙 _, Category.id_comp _⟩
  obtain ⟨j, hj⟩ := kernel_le_maximalTorus centre G hrG S hsS hmS Q.centre hcentreQ
  have hj' : j.hom.hom ≫ S.inclusion.hom.hom = Q.centre.inclusion.hom.hom :=
    congrArg (fun f : Q.centre.group ⟶ G.val => f.hom.hom) hj
  have hqT' : qT.hom.hom ≫ S.inclusion.hom.hom = T.inclusion.hom.hom ≫ q.hom.hom :=
    congrArg (fun f : T.group ⟶ G.val => f.hom.hom) hqT.1
  let z := N.inclusion.hom.hom
  have hz : (z ≫ q.hom.hom) ≫ Q.projection.hom.hom = 1 :=
    (Category.assoc _ _ _).trans (hN.w)
  obtain ⟨w, hw⟩ := (schemeKernel_sections Q.kernel (z ≫ q.hom.hom)).mpr hz
  change w ≫ Q.centre.inclusion.hom.hom = z ≫ q.hom.hom at hw
  let v := w ≫ j.hom.hom
  let a := pullback.snd qT.hom.hom v
  let t := pullback.fst qT.hom.hom v
  have ha := (Over.forget (Spec (CommRingCat.of k))).map_isPullback
    (IsPullback.of_hasPullback qT.hom.hom v)
  have hf : Flat a.left := MorphismProperty.of_isPullback ha hqT.2.1
  have hsurj : Surjective a.left := MorphismProperty.of_isPullback ha hqT.2.2
  have ht : t ≫ qT.hom.hom = a ≫ v := pullback.condition
  have htq : (t ≫ T.inclusion.hom.hom) ≫ q.hom.hom = (a ≫ z) ≫ q.hom.hom := by
    rw [Category.assoc, ← hqT', ← Category.assoc, ht, Category.assoc]
    simp only [v, Category.assoc, hj', hw]
  have htG : Centralizes (𝟙 G.val) (t ≫ qT.hom.hom ≫ S.inclusion.hom.hom) := by
    rw [← Category.assoc, ht]
    apply (Q.isCentre _ _).mpr
    refine ⟨a ≫ w, ?_⟩
    simp only [v, Category.assoc, hj']
  have : IsAffine H.val.X.left := H.property.1
  have : IsClosedImmersion z.left := N.isClosedImmersion
  have : IsAffine N.group.X.left := isAffine_of_isAffineHom z.left
  have : IsFinite qT.hom.hom.left := finiteTorusRestriction hq.1 hqT
  have : IsAffineHom a.left :=
    MorphismProperty.of_isPullback ha (inferInstance : IsAffineHom qT.hom.hom.left)
  have : IsAffine (pullback qT.hom.hom v).left := isAffine_of_isAffineHom a.left
  have htH := centre_of_torus_lift hrH hrG hsT hmT hsS hmS hroots.2.2 t htG
  obtain ⟨n, hn⟩ := (schemeKernel_eq_iff hK (t ≫ T.inclusion.hom.hom) (a ≫ z)).mp htq
  have hz_eq : a ≫ z = (t ≫ T.inclusion.hom.hom) * (n ≫ K.inclusion.hom.hom) := by
    rw [hn, mul_inv_cancel_left]
  have hzH : Centralizes (𝟙 H.val) z := by
    apply centralizes_of_cover hf hsurj
    apply (centralizes_iff _ _).mpr
    intro U g x
    rw [hz_eq, MonObj.comp_mul]
    exact ((centralizes_iff _ _).mp htH U g x).mul_left
      (by simpa only [Category.assoc] using (centralizes_iff _ _).mp hcentralK U (g ≫ n) x)
  intro U g
  rw [show (∃ n : U ⟶ N.group.X, n ≫ z = g) ↔
      g ≫ (q ≫ Q.projection).hom.hom = 1 from schemeKernel_sections hN g]
  constructor
  · intro hg
    have h := centralizes_image q hq.2.1 hq.2.2.1 g hg
    obtain ⟨p, hp⟩ := (Q.isCentre _ _).mp h
    exact (Category.assoc _ _ _).symm.trans
      ((schemeKernel_sections Q.kernel (g ≫ q.hom.hom)).mp ⟨p, hp⟩)
  · intro hg
    obtain ⟨n, hn⟩ := (schemeKernel_sections hN g).mpr hg
    change n ≫ z = g at hn
    rw [← hn]
    apply (centralizes_iff _ _).mpr
    intro V s x
    simpa only [Category.assoc] using (centralizes_iff _ _).mp hzH V (s ≫ n) x

/-- A section of the adjoint quotient acts locally by conjugation by any
representative of that section. -/
private theorem scalarAut_eq_inner_of_lift {H J : GroupScheme k} (p : H ⟶ J)
    (inn : groupSections J ⟶ automorphisms H)
    (onLift : ∀ (V : SchemeOver k) (g : V ⟶ H.X),
      inn.app (op V) ⟨g ≫ p.hom.hom⟩ = innerAut g)
    (x : (groupSections J).obj (op (𝟙_ (SchemeOver k)))) (c : Aut H)
    (hc : scalarAut c (𝟙_ (SchemeOver k)) = inn.app _ x)
    {V : SchemeOver k} (g : V ⟶ H.X) (hg : g ≫ p.hom.hom = toUnit V ≫ x.down) :
    scalarAut c V = innerAut g := by
  let a := toUnit V
  have hnat := NatTrans.naturality_apply inn a.op x
  change inn.app (op V) ⟨a ≫ x.down⟩ = restrictAut a (inn.app _ x) at hnat
  calc
    scalarAut c V = restrictAut a (scalarAut c (𝟙_ (SchemeOver k))) := rfl
    _ = restrictAut a (inn.app _ x) := congrArg (restrictAut a) hc
    _ = inn.app (op V) ⟨a ≫ x.down⟩ := hnat.symm
    _ = innerAut g := hg ▸ onLift V g

private theorem scalarAut_apply_of_eq_inner {H : GroupScheme k} (c : Aut H)
    {V : SchemeOver k} {g : V ⟶ H.X} (h : scalarAut c V = innerAut g) (v : V ⟶ H.X) :
    v ≫ c.asIso.hom.hom.hom = g * v * g⁻¹ := by
  have he := congrArg (fun a : RelativeAut H V => a.asIso.hom.app (op (Over.mk (𝟙 V))) v) h
  change v ≫ c.asIso.hom.hom.hom = (𝟙 V ≫ g) * v * (𝟙 V ≫ g)⁻¹ at he
  simpa only [Category.id_comp] using he

private theorem scalarAut_terminal_surjective (H : GroupScheme k) :
    Function.Surjective (fun c : Aut H => scalarAut c (𝟙_ (SchemeOver k))) := by
  let I := 𝟙_ (SchemeOver k)
  let F := (Over.forget I).op
  let : F.IsEquivalence := (equivToOverUnit (SchemeOver k)).op.isEquivalence_functor
  let L := (Functor.whiskeringLeft _ _ GrpCat.{u}).obj F
  let ff : (yonedaGrp ⋙ L).FullyFaithful :=
    yonedaGrpFullyFaithful.comp (Functor.FullyFaithful.ofFullyFaithful L)
  intro a
  refine ⟨Aut.of (ff.preimageIso a.asIso), ?_⟩
  apply Aut.ext
  apply Iso.ext
  exact ff.map_preimage a.asIso.hom

set_option maxHeartbeats 550000 in
theorem innerAutomorphismLifting : InnerAutomorphismLifting.{u} := by
  intro k _ H G hH hG T S hsT hmT hsS hmS q qT hq hqT Q inn onLift x b hb
  let p := q ≫ Q.projection
  let : IsAffine Q.quotient.val.X.left := Q.quotient.property.1
  obtain ⟨Z, hZ⟩ := schemeKernel_exists p
  let : IsFinite q.hom.hom.left := hq.1
  let : Flat q.hom.hom.left := hq.2.1
  let : Surjective q.hom.hom.left := hq.2.2.1
  let : LocallyOfFiniteType G.val.X.hom := G.property.2.1
  let : IsLocallyNoetherian G.val.X.left := LocallyOfFiniteType.isLocallyNoetherian G.val.X.hom
  let : Flat Q.projection.hom.hom.left := Q.fppf.1
  let : Surjective Q.projection.hom.hom.left := Q.fppf.2.1
  let : LocallyOfFinitePresentation Q.projection.hom.hom.left := Q.fppf.2.2
  have hp : Fppf.IsFppf p.hom.hom.left := by
    change Fppf.IsFppf (q.hom.hom.left ≫ Q.projection.hom.hom.left)
    exact ⟨inferInstance, inferInstance, inferInstance⟩
  let QH : AdjointQuotient H :=
    ⟨Z, compositeKernel_isCentre hH hG hsT hmT hsS hmS hq hqT Q Z hZ, Q.quotient, p, hp, hZ⟩
  obtain ⟨innH, onLiftH, _⟩ := adjointInner H QH
  obtain ⟨c, hc⟩ := scalarAut_terminal_surjective H.val (innH.app _ x)
  let v := toUnit H.val.X ≫ x.down
  let a := pullback.snd p.hom.hom v
  let g := pullback.fst p.hom.hom v
  have : Epi a := pullbackSnd_epi hp.1 hp.2.1 v
  have hg : g ≫ p.hom.hom = toUnit (pullback p.hom.hom v) ≫ x.down := by
    rw [pullback.condition (f := p.hom.hom) (g := v)]
    simp only [v, CategoryTheory.CartesianMonoidalCategory.comp_toUnit_assoc]
  have hc' := scalarAut_eq_inner_of_lift p innH onLiftH x c hc g hg
  have hb' := scalarAut_eq_inner_of_lift Q.projection inn onLift x b hb
    (g ≫ q.hom.hom) ((Category.assoc _ _ _).trans hg)
  have hc'' := scalarAut_apply_of_eq_inner c hc' a
  have hb'' := scalarAut_apply_of_eq_inner b hb' (a ≫ q.hom.hom)
  refine ⟨c, Grp.hom_ext _ _ ((cancel_epi a).mp ?_)⟩
  change a ≫ c.asIso.hom.hom.hom ≫ q.hom.hom =
    a ≫ q.hom.hom ≫ b.asIso.hom.hom.hom
  rw [← Category.assoc, hc'', ← Category.assoc, hb'',
    MonObj.mul_comp, MonObj.mul_comp, GrpObj.inv_comp]

end

end LinearAlgebraicGroups.Arithmetic.CentralCoverInnerLift
