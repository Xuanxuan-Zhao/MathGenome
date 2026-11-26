import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Solvable.SchemeDerivedGroup
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Flag.NormalAffineQuotient
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Affine.Components
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Solvable.FiniteWordClosure
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Solvable.WordDomainGeometry
import Batteries.Tactic.OpenPrivate

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj commutatorElement

universe u

namespace LinearAlgebraicGroups

noncomputable section

namespace SchemeDerivedGroup

abbrev commutatorMap : Specs.SchemeDerivedGroup.CommutatorMapType.{u} :=
  @Specs.SchemeDerivedGroup.commutatorMap

abbrev IsDerivedSubgroup : Specs.SchemeDerivedGroup.IsDerivedSubgroupType.{u} :=
  @Specs.SchemeDerivedGroup.IsDerivedSubgroup

abbrev IsSolvable : Specs.SchemeDerivedGroup.GroupPredicateType.{u} :=
  @Specs.SchemeDerivedGroup.IsSolvable

abbrev IsSplitSolvable : Specs.SchemeDerivedGroup.GroupPredicateType.{u} :=
  @Specs.SchemeDerivedGroup.IsSplitSolvable

abbrev DerivedSeries : Specs.SchemeDerivedGroup.DerivedSeriesType.{u} :=
  @Specs.SchemeDerivedGroup.DerivedSeries

abbrev LowerCentralSeries : Specs.SchemeDerivedGroup.LowerCentralSeriesType.{u} :=
  @Specs.SchemeDerivedGroup.LowerCentralSeries


open _root_.LinearAlgebraicGroups.Specs (SubgroupSections)
open Specs.SchemeDerivedGroup (IsNormalClosure FactorsThrough IsSubgroupOf)

open private groupPresentation
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Affine.SchemeImageQuotient
open private normalSubgroup_of_iso from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Flag.NormalAffineQuotient

set_option maxHeartbeats 3000000
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

variable {k : Type u} [Field k]

private theorem subgroupFactors_comp {G : GroupScheme k} {H N : ClosedSubgroup G}
    {T : SchemeOver k} {f : T ⟶ G.X} (h : FactorsThrough H f) (hn : IsSubgroupOf H N) :
    FactorsThrough N f := by
  obtain ⟨t, ht⟩ := h
  obtain ⟨b, hb⟩ := hn
  change (t : T ⟶ H.group.X) ≫ H.inclusion.hom.hom = f at ht
  have hb' : b.hom.hom ≫ N.inclusion.hom.hom = H.inclusion.hom.hom :=
    congrArg (Grp.forget (SchemeOver k)).map hb
  exact ⟨t ≫ b.hom.hom, (Category.assoc _ _ _).trans ((congrArg (t ≫ ·) hb').trans ht)⟩

private abbrev hopfSubgroup (A : HopfAlgebraCategory k) (I : Ideal A) [I.IsHopfIdeal k] :
    ClosedSubgroup (specGroup A) :=
  ⟨_, specGroupMap (hopfQuotientMap A I),
    (hopfMapClosedImmersion k _).mpr Ideal.Quotient.mk_surjective⟩

private theorem normalClosureExists_spec (A : HopfAlgebraCategory k) {X : SchemeOver k}
    (f : X ⟶ (specGroup A).X) : ∃ D : ClosedSubgroup (specGroup A), IsNormalClosure f D := by
  classical
  let Index := {I : Ideal A // ∃ h : I.IsHopfIdeal k,
    letI := h
    let H := hopfSubgroup A I
    IsNormalSubgroup H.inclusion ∧ FactorsThrough H f}
  let I (i : Index) : Ideal A := i.val
  let hI (i : Index) : (I i).IsHopfIdeal k := i.property.choose
  let H (i : Index) := hopfSubgroup A (I i)
  have hn (i : Index) : IsNormalSubgroup (H i).inclusion := i.property.choose_spec.1
  have hf (i : Index) : FactorsThrough (H i) f := i.property.choose_spec.2
  obtain ⟨hJ, p, hp, ⟨_⟩, ⟨hlim⟩⟩ := subgroupFamilyIntersection k A I
  let J : Ideal A := ⨆ i, I i
  let D := hopfSubgroup A J
  have hp' (i : Index) : p i ≫ (H i).inclusion = D.inclusion := hp i
  let V := Grp.forget (SchemeOver k)
  have lift {T : SchemeOver k} (t : T ⟶ (specGroup A).X)
      (ht : ∀ i, FactorsThrough (H i) t) : FactorsThrough D t := by
    let π (i : Index) : T ⟶ (H i).group.X := (ht i).choose
    have hπ (i : Index) : π i ≫ (H i).inclusion.hom.hom = t := (ht i).choose_spec
    let F := WidePullbackShape.wideCospan (specGroup A)
      (fun i ↦ (H i).group) (fun i ↦ (H i).inclusion)
    let c : Cone (F ⋙ V) := WidePullbackShape.mkCone t π hπ
    refine ⟨hlim.lift c, ?_⟩
    exact hlim.fac c none
  refine ⟨D, ?_, lift f hf, ?_⟩
  · let g := fst (specGroup A).X D.group.X
    let d := snd (specGroup A).X D.group.X
    apply lift (Specs.subgroupConjugation D.inclusion)
    intro i
    obtain ⟨s, hs⟩ := normalSubgroup_conjugate_sections (hn i) g (d ≫ (p i).hom.hom)
    refine ⟨s, hs.trans ?_⟩
    have hi : (p i).hom.hom ≫ (H i).inclusion.hom.hom = D.inclusion.hom.hom :=
      congrArg V.map (hp' i)
    change g * ((d ≫ (p i).hom.hom) ≫ (H i).inclusion.hom.hom) * g⁻¹ =
      g * (d ≫ D.inclusion.hom.hom) * g⁻¹
    rw [Category.assoc, hi]
  · intro N hN hNf
    obtain ⟨L, ⟨hL, e, he⟩, _⟩ :=
      (closedSubgroupClassification k A N.group N.inclusion).mp N.isClosedImmersion
    let H' := hopfSubgroup A L
    have hn' : IsNormalSubgroup H'.inclusion :=
      normalSubgroup_of_iso (Iso.refl _) e.symm (by simp [H', ← he, ← Category.assoc]) hN
    have hf' : FactorsThrough H' f :=
      subgroupFactors_comp hNf ⟨e.hom, he⟩
    let i : Index := ⟨L, hL, hn', hf'⟩
    refine ⟨p i ≫ e.inv, ?_⟩
    have hh : e.inv ≫ N.inclusion = (H i).inclusion := by
      rw [← he, Iso.inv_hom_id_assoc]
    rw [Category.assoc, hh, hp']

theorem normalClosureExists : Specs.SchemeDerivedGroup.NormalClosureExists.{u} := by
  intro k _ G X f
  obtain ⟨A, _, ⟨e⟩⟩ := groupPresentation G
  let F := Grp.forget (SchemeOver k)
  let W := Over.forget (Spec (CommRingCat.of k))
  let e' : (specGroup A).X ≅ G.val.X := F.mapIso e
  obtain ⟨D, hDn, ⟨d, hd⟩, hDmin⟩ := normalClosureExists_spec A (f ≫ e'.inv)
  have hD : IsClosedImmersion D.inclusion.hom.hom.left := D.isClosedImmersion
  have he : IsIso ((F ⋙ W).map e.hom) := Functor.map_isIso _ _
  let D' : ClosedSubgroup G.val :=
    ⟨D.group, D.inclusion ≫ e.hom, IsClosedImmersion.comp _ ((F ⋙ W).map e.hom)⟩
  refine ⟨D', normalSubgroup_of_iso e.symm (Iso.refl _) (by simp [D']) hDn, ⟨d, ?_⟩, ?_⟩
  · change d ≫ D.inclusion.hom.hom ≫ e'.hom = f
    change d ≫ D.inclusion.hom.hom = f ≫ e'.inv at hd
    rw [← Category.assoc, hd, Category.assoc, Iso.inv_hom_id, Category.comp_id]
  · intro N hN hNf
    have hi : IsClosedImmersion N.inclusion.hom.hom.left := N.isClosedImmersion
    have hei : IsIso ((F ⋙ W).map e.inv) := Functor.map_isIso _ _
    let N' : ClosedSubgroup (specGroup A) :=
      ⟨N.group, N.inclusion ≫ e.inv, IsClosedImmersion.comp _ ((F ⋙ W).map e.inv)⟩
    obtain ⟨n, hn⟩ := hNf
    have hn' : FactorsThrough N' (f ≫ e'.inv) := by
      refine ⟨n, ?_⟩
      change n ≫ N.inclusion.hom.hom ≫ e'.inv = f ≫ e'.inv
      change n ≫ N.inclusion.hom.hom = f at hn
      rw [← Category.assoc, hn]
    obtain ⟨a, ha⟩ := hDmin N'
      (normalSubgroup_of_iso e (Iso.refl _) (by simp [N']) hN) hn'
    refine ⟨a, ?_⟩
    change a ≫ N.inclusion ≫ e.inv = D.inclusion at ha
    change a ≫ N.inclusion = D.inclusion ≫ e.hom
    simpa only [Category.assoc, Iso.inv_hom_id, Category.comp_id] using
      (congrArg (· ≫ e.hom) ha)

theorem derivedSubgroupExists : Specs.SchemeDerivedGroup.DerivedSubgroupExists.{u} :=
  fun G ↦ normalClosureExists G _


open _root_.LinearAlgebraicGroups.Specs (IsSchemeKernel schemeFppfSheaf fppfOver rightQuotientProjection
  rightQuotientSheaf rightCosetPresheaf rightCosetProjection)
open Specs.SchemeDerivedGroup (RepresentsQuotient IsCommutative)
open private schemeKernel_exists schemeKernel_sections fppfYoneda_locallySurjective
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Affine.SchemeImageQuotient
open private isMonHom_of_affinePoints from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Affine.ClosedSubgroups

private theorem comp_commutatorMap {G A B : GroupScheme k}
    (a : A ⟶ G) (b : B ⟶ G) {T : SchemeOver k}
    (x : T ⟶ A.X) (y : T ⟶ B.X) :
    lift x y ≫ commutatorMap a b =
      ⁅x ≫ a.hom.hom, y ≫ b.hom.hom⁆ := by
  simp only [commutatorMap, Specs.SchemeDerivedGroup.commutatorMap, commutatorElement_def, MonObj.comp_mul, GrpObj.comp_inv,
    ← Category.assoc, lift_fst, lift_snd]

private theorem kernel_normal {G H : GroupScheme k} {f : G ⟶ H} {N : ClosedSubgroup G}
    (hn : IsSchemeKernel f N) : IsNormalSubgroup N.inclusion := by
  change FactorsThrough N (Specs.subgroupConjugation N.inclusion)
  apply (schemeKernel_sections hn _).2
  let T := G.X ⊗ N.group.X
  let F : (T ⟶ G.X) →* (T ⟶ H.X) := ((yonedaGrp.map f).app (op T)).hom
  let x : T ⟶ G.X := fst _ _
  let y : T ⟶ G.X := snd _ _ ≫ N.inclusion.hom.hom
  have hy : F y = 1 := (schemeKernel_sections hn y).1 ⟨snd _ _, rfl⟩
  change F (x * y * x⁻¹) = 1
  rw [map_mul, map_mul, map_inv, hy, mul_one, mul_inv_cancel]

private theorem locallySurjective_pair_ext {G Q : GroupScheme k} {Z T : SchemeOver k}
    (q : G ⟶ Q) (hq : Presheaf.IsLocallySurjective (fppfOver k)
      ((fppfOver k).uliftYoneda.{u + 1}.map q.hom.hom).hom)
    (x y : T ⟶ Q.X) {r s : T ⟶ Z}
    (h : ∀ {U : SchemeOver k} (a : U ⟶ T) (x' y' : U ⟶ G.X),
      x' ≫ q.hom.hom = a ≫ x → y' ≫ q.hom.hom = a ≫ y → a ≫ r = a ≫ s) :
    r = s := by
  let J := fppfOver k
  let φ := (J.uliftYoneda.{u + 1}.map q.hom.hom).hom
  let x₀ : (schemeFppfSheaf Q.X).obj.obj (op T) := ULift.up x
  let y₀ : (schemeFppfSheaf Q.X).obj.obj (op T) := ULift.up y
  have hc : Presheaf.imageSieve φ x₀ ⊓ Presheaf.imageSieve φ y₀ ∈ J T :=
    J.intersection_covering (hq.imageSieve_mem x₀) (hq.imageSieve_mem y₀)
  have hs := ((isSheaf_iff_isSheaf_of_type _ _).1 (schemeFppfSheaf Z).property).isSeparated _ hc
  apply congrArg ULift.down (hs.ext (t₁ := ULift.up r) (t₂ := ULift.up s) ?_)
  intro U a ha
  obtain ⟨⟨x'⟩, hx'⟩ := ha.1
  obtain ⟨⟨y'⟩, hy'⟩ := ha.2
  exact congrArg ULift.up (h a x' y' (congrArg ULift.down hx') (congrArg ULift.down hy'))

private theorem quotient_commutative {G Q : GroupScheme k} {D : ClosedSubgroup G}
    (q : G ⟶ Q) (hq : IsSchemeKernel q D)
    (hl : Presheaf.IsLocallySurjective (fppfOver k)
      ((fppfOver k).uliftYoneda.{u + 1}.map q.hom.hom).hom)
    (hd : IsDerivedSubgroup D) : IsCommutative Q := by
  intro T x y
  apply locallySurjective_pair_ext q hl x y
  intro U a x' y' hx hy
  have hf : ∃ d : G.X ⊗ G.X ⟶ D.group.X,
      d ≫ D.inclusion.hom.hom = commutatorMap (𝟙 G) (𝟙 G) := hd.2.1
  obtain ⟨d, he⟩ := hf
  have hc : FactorsThrough D ⁅x', y'⁆ := by
    refine ⟨lift x' y' ≫ d, ?_⟩
    change (lift x' y' ≫ d) ≫ D.inclusion.hom.hom = _
    rw [Category.assoc, he, comp_commutatorMap]
    simp
  let F : (U ⟶ G.X) →* (U ⟶ Q.X) := ((yonedaGrp.map q).app (op U)).hom
  have hc' : F ⁅x', y'⁆ = 1 := (schemeKernel_sections hq _).1 hc
  rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm] at hc'
  change (x' ≫ q.hom.hom) * (y' ≫ q.hom.hom) =
    (y' ≫ q.hom.hom) * (x' ≫ q.hom.hom) at hc'
  simpa only [hx, hy, MonObj.comp_mul] using hc'

private def cosetMapToGroup {G L : GroupScheme k} (D : ClosedSubgroup G)
    (f : G ⟶ L) (hk : ∀ {T : SchemeOver k} (t : T ⟶ G.X),
      FactorsThrough D t → t ≫ f.hom.hom = 1) :
    rightCosetPresheaf D ⟶ (schemeFppfSheaf L.X).obj where
  app T := ↾fun x ↦ Quotient.lift
    (fun g : T.unop ⟶ G.X ↦ ULift.up (g ≫ f.hom.hom))
    (fun g g' hg ↦ by
      apply congrArg ULift.up
      let F := ((yonedaGrp.map f).app T).hom
      have h : F (g⁻¹ * g') = 1 := hk _ (QuotientGroup.leftRel_apply.mp hg)
      rwa [map_mul, map_inv, inv_mul_eq_one] at h) x.down
  naturality T U b := by
    ext ⟨x⟩
    induction x using QuotientGroup.induction_on with
    | H g =>
      change ULift.up ((b.unop ≫ g) ≫ f.hom.hom) = ULift.up (b.unop ≫ g ≫ f.hom.hom)
      rw [Category.assoc]


private theorem quotient_underlying_desc {G Q L : GroupScheme k}
    (D : ClosedSubgroup G) (q : G ⟶ Q) (hQ : RepresentsQuotient D q)
    (f : G ⟶ L) (hk : ∀ {T : SchemeOver k} (t : T ⟶ G.X),
      FactorsThrough D t → t ≫ f.hom.hom = 1) :
    ∃ d : Q.X ⟶ L.X, q.hom.hom ≫ d = f.hom.hom := by
  obtain ⟨e, he⟩ := hQ
  let J := fppfOver k
  let Y := J.uliftYoneda.{u + 1}
  let C := cosetMapToGroup D f hk
  let g₀ : rightQuotientSheaf D ⟶ schemeFppfSheaf L.X :=
    ⟨sheafifyLift J C (schemeFppfSheaf L.X).property⟩
  let d : Q.X ⟶ L.X := (J.fullyFaithfulUliftYoneda).preimage (e.inv ≫ g₀)
  have hd : Y.map d = e.inv ≫ g₀ := J.fullyFaithfulUliftYoneda.map_preimage _
  refine ⟨d, Y.map_injective ?_⟩
  rw [Y.map_comp, hd, ← he, ← Category.assoc, Category.assoc (rightQuotientProjection D),
    Iso.hom_inv_id, Category.comp_id]
  apply Sheaf.hom_ext
  change (rightCosetProjection D ≫ toSheafify J _) ≫ g₀.hom = _
  rw [Category.assoc, toSheafify_sheafifyLift]
  rfl

private theorem quotient_desc_monoid {G L : GroupScheme k} (Q : AffineAlgebraicGroup k)
    (q : G ⟶ Q.val) (hloc : Presheaf.IsLocallySurjective (fppfOver k)
      ((fppfOver k).uliftYoneda.{u + 1}.map q.hom.hom).hom)
    (f : G ⟶ L) (d : Q.val.X ⟶ L.X) (hqg : q.hom.hom ≫ d = f.hom.hom) :
    IsMonHom d := by
  apply isMonHom_of_affinePoints _ Q.property.1
  intro R x y
  apply locallySurjective_pair_ext q hloc x y
  intro U a x' y' hx hy
  change (a ≫ (x * y)) ≫ d = a ≫ ((x ≫ d) * (y ≫ d))
  rw [MonObj.comp_mul, MonObj.comp_mul, ← Category.assoc, ← Category.assoc, ← hx, ← hy]
  let P : (U ⟶ G.X) →* (U ⟶ Q.val.X) := ((yonedaGrp.map q).app (op U)).hom
  let F : (U ⟶ G.X) →* (U ⟶ L.X) := ((yonedaGrp.map f).app (op U)).hom
  have hfd (s : U ⟶ G.X) : P s ≫ d = F s :=
    (Category.assoc _ _ _).trans (congrArg (s ≫ ·) hqg)
  change (P x' * P y') ≫ d = (P x' ≫ d) * (P y' ≫ d)
  rw [← map_mul, hfd, hfd, hfd, map_mul]

private theorem quotient_desc {G L : GroupScheme k} (Q : AffineAlgebraicGroup k)
    (D : ClosedSubgroup G) (q : G ⟶ Q.val) (hQ : RepresentsQuotient D q)
    (hloc : Presheaf.IsLocallySurjective (fppfOver k)
      ((fppfOver k).uliftYoneda.{u + 1}.map q.hom.hom).hom)
    (f : G ⟶ L) (hk : ∀ {T : SchemeOver k} (t : T ⟶ G.X),
      FactorsThrough D t → t ≫ f.hom.hom = 1) :
    ∃! g : Q.val ⟶ L, q ≫ g = f := by
  obtain ⟨d, hqg⟩ := quotient_underlying_desc D q hQ f hk
  have hm := quotient_desc_monoid Q q hloc f d hqg
  let g := Grp.homMk d
  have hg : q ≫ g = f := Grp.hom_ext _ _ hqg
  refine ⟨g, hg, ?_⟩
  intro g' hg'
  refine Grp.hom_ext g' g ?_
  apply locallySurjective_pair_ext q hloc (𝟙 Q.val.X) (𝟙 Q.val.X)
  intro U a x' _ hx _
  change x' ≫ q.hom.hom = a ≫ 𝟙 Q.val.X at hx
  rw [Category.comp_id] at hx
  have he : q.hom.hom ≫ g'.hom.hom = q.hom.hom ≫ g.hom.hom :=
    congrArg (Grp.forget (SchemeOver k)).map (hg'.trans hg.symm)
  rw [← hx, Category.assoc, Category.assoc, he]

theorem abelianization : Specs.SchemeDerivedGroup.Abelianization.{u} := by
  intro k _ G D hd
  obtain ⟨L, f, Q, q, i, _, hq, hi, _, hrep⟩ := normalAffineQuotient G D hd.1
  obtain ⟨_, hflat, hsurj, hfp, _, _⟩ := hi
  have hl := fppfYoneda_locallySurjective q.hom.hom
  refine ⟨Q, q, hq, hrep, quotient_commutative q hq hl hd, ?_⟩
  intro L' hc f'
  have hL' := L'.property.1
  obtain ⟨N, hN⟩ := schemeKernel_exists f'
  have hf : FactorsThrough N (commutatorMap (𝟙 G.val) (𝟙 G.val)) := by
    apply (schemeKernel_sections hN _).2
    let T := G.val.X ⊗ G.val.X
    let F : (T ⟶ G.val.X) →* (T ⟶ L'.val.X) := ((yonedaGrp.map f').app (op T)).hom
    let x : T ⟶ G.val.X := fst _ _
    let y : T ⟶ G.val.X := snd _ _
    have h : F ⁅x, y⁆ = 1 := by
      rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
      exact hc T _ _
    change F (commutatorMap (𝟙 G.val) (𝟙 G.val)) = 1
    have hi : (𝟙 G.val : G.val ⟶ G.val).hom.hom = 𝟙 G.val.X := rfl
    have he : commutatorMap (𝟙 G.val) (𝟙 G.val) = ⁅x, y⁆ := by
      simp only [commutatorMap, Specs.SchemeDerivedGroup.commutatorMap, x, y, hi, Category.comp_id, commutatorElement_def]
    rw [he]
    exact h
  apply quotient_desc Q D q hrep hl f'
  intro T t ht
  exact (schemeKernel_sections hN t).1 (subgroupFactors_comp ht (hd.2.2 N (kernel_normal hN) hf))


theorem normalClosure_unique {G : GroupScheme k} {X : SchemeOver k} {f : X ⟶ G.X}
    {D E : ClosedSubgroup G} (hd : IsNormalClosure f D) (he : IsNormalClosure f E) :
    ∃ e : D.group ≅ E.group, e.hom ≫ E.inclusion = D.inclusion := by
  obtain ⟨i, hi⟩ := hd.2.2 E he.1 he.2.1
  obtain ⟨j, hj⟩ := he.2.2 D hd.1 hd.2.1
  let F := Grp.forget (SchemeOver k) ⋙ Over.forget (Spec (CommRingCat.of k))
  have hd' : IsClosedImmersion (F.map D.inclusion) := D.isClosedImmersion
  have he' : IsClosedImmersion (F.map E.inclusion) := E.isClosedImmersion
  have hmd : Mono D.inclusion := F.mono_of_mono_map inferInstance
  have hme : Mono E.inclusion := F.mono_of_mono_map inferInstance
  refine ⟨⟨i, j, ?_, ?_⟩, hi⟩
  · apply (cancel_mono D.inclusion).mp
    rw [Category.assoc, hj, hi, Category.id_comp]
  · apply (cancel_mono E.inclusion).mp
    rw [Category.assoc, hi, hj, Category.id_comp]

/-- A choice of the least closed normal subgroup containing the commutator morphism. -/
def derivedSubgroup (G : AffineAlgebraicGroup k) :
    { D : ClosedSubgroup G.val // IsDerivedSubgroup D } :=
  ⟨(derivedSubgroupExists G).choose, (derivedSubgroupExists G).choose_spec⟩

theorem lowerCentralSeriesExists : Specs.SchemeDerivedGroup.LowerCentralSeriesExists.{u} := by
  intro k _ G n
  induction n with
  | zero =>
    let D : ClosedSubgroup G.val :=
      ⟨G.val, 𝟙 G.val, inferInstanceAs (IsClosedImmersion (𝟙 G.val.X.left))⟩
    exact ⟨D, Specs.SchemeDerivedGroup.LowerCentralSeries.zero D (inferInstanceAs (IsIso (𝟙 G.val)))⟩
  | succ n ih =>
    obtain ⟨H, hH⟩ := ih
    obtain ⟨D, hD⟩ := normalClosureExists G (commutatorMap (𝟙 G.val) H.inclusion)
    exact ⟨D, Specs.SchemeDerivedGroup.LowerCentralSeries.succ hH D hD⟩

theorem lowerCentralSeries_normal {G : GroupScheme k} {n : ℕ} {D : ClosedSubgroup G}
    (h : LowerCentralSeries G n D) : IsNormalSubgroup D.inclusion := by
  cases h with
  | zero D hi =>
    have h : IsIso D.inclusion.hom.hom := (Grp.forget (SchemeOver k)).map_isIso D.inclusion
    exact ⟨Specs.subgroupConjugation D.inclusion ≫ inv D.inclusion.hom.hom, by simp⟩
  | succ _ _ hs => exact hs.1

theorem commutatorSubgroupLe : Specs.SchemeDerivedGroup.CommutatorSubgroupLe.{u} := by
  intro k _ G D hD T
  rw [commutator, Subgroup.commutator_le]
  intro x _ y _
  obtain ⟨d, hd⟩ : FactorsThrough D (commutatorMap (𝟙 G) (𝟙 G)) := hD.2.1
  change d ≫ D.inclusion.hom.hom = commutatorMap (𝟙 G) (𝟙 G) at hd
  refine ⟨lift x y ≫ d, ?_⟩
  change (lift x y ≫ d) ≫ D.inclusion.hom.hom = ⁅x, y⁆
  rw [Category.assoc, hd, comp_commutatorMap]
  simp


private abbrev closedSubgroupAlgebraic (G : AffineAlgebraicGroup k) (D : ClosedSubgroup G.val) :
    AffineAlgebraicGroup k := by
  have hG := G.property.1
  have hf := G.property.2.1
  have hq := G.property.2.2
  have hi : IsClosedImmersion D.inclusion.hom.hom.left := D.isClosedImmersion
  refine ⟨D.group, isAffine_of_isAffineHom D.inclusion.hom.hom.left, ?_, ?_⟩
  · rw [← Over.w D.inclusion.hom.hom]
    infer_instance
  · rw [← Over.w D.inclusion.hom.hom]
    infer_instance

theorem derivedSeriesExists : Specs.SchemeDerivedGroup.DerivedSeriesExists.{u} := by
  intro k _ G n
  induction n with
  | zero => exact ⟨G, Specs.SchemeDerivedGroup.DerivedSeries.zero⟩
  | succ n ih =>
    obtain ⟨H, hH⟩ := ih
    obtain ⟨D, hD⟩ := derivedSubgroupExists H
    exact ⟨closedSubgroupAlgebraic H D, Specs.SchemeDerivedGroup.DerivedSeries.succ hH D hD⟩

open private geometricallyConnected_of_connected
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Solvable.WordDomainGeometry

private theorem connected_product (G : AffineAlgebraicGroup k) {X : SchemeOver k}
    [ConnectedSpace G.val.X.left] [ConnectedSpace X.left] :
    ConnectedSpace (G.val.X ⊗ X).left := by
  have hG := G.property.2.1
  have hGeom := geometricallyConnected_of_connected G
  change ConnectedSpace ↥(pullback G.val.X.hom X.hom)
  infer_instance

private theorem factor_identityComponent {H N : GroupScheme k} {i : H ⟶ N}
    {X : SchemeOver k} [ConnectedSpace X.left] [IsOpenImmersion i.hom.hom.left]
    (hi : Set.range i.hom.hom.left =
      connectedComponent ((η[N.X]).left (IsLocalRing.closedPoint k)))
    (f : X ⟶ N.X) (x : 𝟙_ (SchemeOver k) ⟶ X) (hx : x ≫ f = 1) :
    ∃ f' : X ⟶ H.X, f' ≫ i.hom.hom = f := by
  have hne : (η[N.X]).left (IsLocalRing.closedPoint k) ∈ Set.range f.left := by
    refine ⟨x.left (IsLocalRing.closedPoint k), ?_⟩
    have e := congrArg (fun p : 𝟙_ (SchemeOver k) ⟶ N.X ↦ p.left (IsLocalRing.closedPoint k)) hx
    simpa only [Over.comp_left, Scheme.Hom.comp_apply, show (1 : (𝟙_ (SchemeOver k)) ⟶ N.X) =
      η[N.X] from (MonObj.one_eq_one (M := N.X)).symm] using e
  have hs : Set.range f.left ⊆ Set.range i.hom.hom.left := by
    rw [hi]
    exact (isConnected_range f.left.continuous).subset_connectedComponent hne
  let g := IsOpenImmersion.lift i.hom.hom.left f.left hs
  have hg := IsOpenImmersion.lift_fac i.hom.hom.left f.left hs
  refine ⟨Over.homMk g ?_, Over.OverMorphism.ext hg⟩
  rw [← Over.w i.hom.hom, ← Category.assoc, hg, Over.w f]

private theorem normalClosure_connected (G : AffineAlgebraicGroup k)
    [ConnectedSpace G.val.X.left] {X : SchemeOver k} [ConnectedSpace X.left]
    {f : X ⟶ G.val.X} {D : ClosedSubgroup G.val} (hd : IsNormalClosure f D)
    (x : 𝟙_ (SchemeOver k) ⟶ X) (hx : x ≫ f = 1) :
    ConnectedSpace D.group.X.left := by
  obtain ⟨Q, H, q, i, h, _, _, _⟩ :=
    identityComponentAndQuotient k (closedSubgroupAlgebraic G D)
  have hi := h.openImmersion
  have hc := h.closedImmersion
  have hr : Set.range i.hom.hom.left =
      connectedComponent ((η[D.group.X]).left (IsLocalRing.closedPoint k)) := by
    have he : Classical.choice (inferInstance : Nonempty (Spec (CommRingCat.of k))) =
        IsLocalRing.closedPoint k := Subsingleton.elim _ _
    simpa only [he] using h.identityComponent
  have hD := D.isClosedImmersion
  have hH : ConnectedSpace H.X.left :=
    @GeometricallyConnected.connectedSpace_of_subsingleton _ _ H.X.hom h.geometricallyConnected
      inferInstance inferInstance
  let N : ClosedSubgroup G.val :=
    ⟨H, i ≫ D.inclusion, IsClosedImmersion.comp i.hom.hom.left D.inclusion.hom.hom.left⟩
  have hN : IsNormalSubgroup N.inclusion := by
    have hp : ConnectedSpace (G.val.X ⊗ H.X).left := connected_product G
    let p := fst G.val.X H.X
    let r := snd G.val.X H.X
    obtain ⟨c, hc⟩ := normalSubgroup_conjugate_sections hd.1 p (r ≫ i.hom.hom)
    have hc' : c ≫ D.inclusion.hom.hom = Specs.subgroupConjugation N.inclusion := by
      rw [hc]
      change p * ((r ≫ i.hom.hom) ≫ D.inclusion.hom.hom) * p⁻¹ =
        p * (r ≫ i.hom.hom ≫ D.inclusion.hom.hom) * p⁻¹
      rw [Category.assoc]
    let e : 𝟙_ (SchemeOver k) ⟶ G.val.X ⊗ H.X := lift 1 1
    have hm : Mono D.inclusion.hom.hom := Over.mono_of_mono_left _
    have he : e ≫ c = 1 := by
      apply (cancel_mono D.inclusion.hom.hom).mp
      rw [Category.assoc, hc']
      simp [e, Specs.subgroupConjugation, MonObj.comp_mul, GrpObj.comp_inv,
        ← Category.assoc]
    obtain ⟨a, ha⟩ := factor_identityComponent (i := i) hr c e he
    exact ⟨a, by
      change a ≫ i.hom.hom ≫ D.inclusion.hom.hom = _
      rw [← Category.assoc, ha, hc']⟩
  have hf : FactorsThrough N f := by
    obtain ⟨d, hu⟩ := hd.2.1
    change d ≫ D.inclusion.hom.hom = f at hu
    have hm : Mono D.inclusion.hom.hom := Over.mono_of_mono_left _
    have he : x ≫ d = 1 := by
      apply (cancel_mono D.inclusion.hom.hom).mp
      rw [Category.assoc, hu, hx]
      simp
    obtain ⟨a, ha⟩ := factor_identityComponent (i := i) hr d x he
    exact ⟨a, by
      change a ≫ i.hom.hom ≫ D.inclusion.hom.hom = f
      rw [← Category.assoc, ha, hu]⟩
  obtain ⟨j, hj⟩ := hd.2.2 N hN hf
  let V := Grp.forget (SchemeOver k) ⋙ Over.forget (Spec (CommRingCat.of k))
  have hm : Mono D.inclusion.hom.hom.left := inferInstance
  have hj₀ : j.hom.hom.left ≫ (i.hom.hom.left ≫ D.inclusion.hom.hom.left) =
      D.inclusion.hom.hom.left := congrArg V.map hj
  have hj' : j.hom.hom.left ≫ i.hom.hom.left = 𝟙 D.group.X.left := by
    apply (cancel_mono D.inclusion.hom.hom.left).mp
    simpa only [Category.id_comp, Category.assoc] using hj₀
  have hs : Function.Surjective i.hom.hom.left := fun y ↦
    ⟨j.hom.hom.left y, congrArg (fun p : D.group.X.left ⟶ D.group.X.left ↦ p y) hj'⟩
  exact hs.connectedSpace i.hom.hom.left.continuous

/-- The terms of the lower central series of a connected affine algebraic group
are connected, over an arbitrary field. -/
theorem lowerCentralSeries_connected (G : AffineAlgebraicGroup k) [ConnectedSpace G.val.X.left]
    {n : ℕ} {D : ClosedSubgroup G.val} (h : LowerCentralSeries G.val n D) :
    ConnectedSpace D.group.X.left := by
  induction h with
  | zero D hd =>
    let V := Grp.forget (SchemeOver k) ⋙ Over.forget (Spec (CommRingCat.of k))
    let e : D.group.X.left ≅ G.val.X.left := V.mapIso (asIso D.inclusion)
    exact e.hom.homeomorph.connectedSpace_iff.mpr inferInstance
  | @succ n H prev D hd ih =>
    have hp := connected_product G (X := H.group.X)
    refine normalClosure_connected G hd (lift 1 1) ?_
    rw [comp_commutatorMap]
    simp

/-- The scheme-theoretic derived subgroup of a connected affine algebraic group
is connected, over an arbitrary field. -/
theorem derivedSubgroup_connected (G : AffineAlgebraicGroup k) [ConnectedSpace G.val.X.left]
    (D : ClosedSubgroup G.val) (hd : IsDerivedSubgroup D) : ConnectedSpace D.group.X.left := by
  have hp := connected_product G (X := G.val.X)
  refine normalClosure_connected G hd (lift 1 1) ?_
  rw [comp_commutatorMap]
  simp

open Specs.FiniteWordClosure (power wordDomain evaluate ConjugationStable)
open private affine_tensor affine_power from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Solvable.FiniteWordClosure
open private geometricallyIrreducible_of_connected smooth_geometricallyIrreducible_tensor
  geometry_of_smooth_geometricallyIrreducible from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Solvable.WordDomainGeometry

private theorem comp_commutatorMap_projections {G A B : GroupScheme k}
    (a : A ⟶ G) (b : B ⟶ G) {T : SchemeOver k} (p : T ⟶ A.X ⊗ B.X) :
    p ≫ commutatorMap a b =
      ⁅p ≫ fst A.X B.X ≫ a.hom.hom, p ≫ snd A.X B.X ≫ b.hom.hom⁆ := by
  simp only [commutatorMap, Specs.SchemeDerivedGroup.commutatorMap, commutatorElement_def,
    MonObj.comp_mul, GrpObj.comp_inv]

private theorem commutatorMap_conjugationStable {G H : GroupScheme k} (i : H ⟶ G)
    (hi : IsNormalSubgroup i) : ConjugationStable (commutatorMap (𝟙 G) i) := by
  intro T g p
  let x := p ≫ fst G.X H.X
  let y := p ≫ snd G.X H.X
  obtain ⟨z, hz⟩ := normalSubgroup_conjugate_sections hi g y
  refine ⟨lift (g * x * g⁻¹) z, ?_⟩
  rw [comp_commutatorMap, comp_commutatorMap_projections, conjugate_commutatorElement]
  have hid : (𝟙 G : G ⟶ G).hom.hom = 𝟙 G.X := rfl
  simp only [hid, Category.comp_id, hz, x, y, Category.assoc]

private theorem power_geometry (X : SchemeOver k) [Smooth X.hom]
    [GeometricallyIrreducible X.hom] (m : ℕ) :
    Smooth (power X m).hom ∧ GeometricallyIrreducible (power X m).hom := by
  induction m with
  | zero =>
    change Smooth (𝟙 (Spec (CommRingCat.of k))) ∧
      GeometricallyIrreducible (𝟙 (Spec (CommRingCat.of k)))
    refine ⟨inferInstance, ⟨?_⟩⟩
    intro K _ a Y fst snd h
    have : IsIso snd := h.isIso_snd_of_isIso
    exact snd.homeomorph.irreducibleSpace_iff.mpr inferInstance
  | succ m ih =>
    obtain ⟨hs, hi⟩ := ih
    exact smooth_geometricallyIrreducible_tensor X (power X m)

-- Build the dominant word map over the given field and identify its image
-- with the least normal subgroup by the universal property.
private theorem commutatorWordClosure [PerfectField k] (G : AffineAlgebraicGroup k)
    (H : AffineAlgebraicGroup k) (i : H.val ⟶ G.val) (hi : IsNormalSubgroup i)
    (hg : Smooth G.val.X.hom) (hgc : ConnectedSpace G.val.X.left)
    (hh : Smooth H.val.X.hom) (hhc : ConnectedSpace H.val.X.left)
    {D : ClosedSubgroup G.val} (hd : IsNormalClosure (commutatorMap (𝟙 G.val) i) D) :
    let X := G.val.X ⊗ H.val.X
    let f := commutatorMap (𝟙 G.val) i
    ∃ (n : ℕ) (w : wordDomain X n ⟶ D.group.X),
      IsAffine (wordDomain X n).left ∧ Smooth (wordDomain X n).hom ∧
      IsSchemeTheoreticallyDominant w.left ∧ Smooth D.group.X.hom ∧
      ∀ (T : SchemeOver k) (p : T ⟶ wordDomain X n),
        p ≫ w ≫ D.inclusion.hom.hom = evaluate f n p := by
  let X := G.val.X ⊗ H.val.X
  let f := commutatorMap (𝟙 G.val) i
  let x₀ : 𝟙_ (SchemeOver k) ⟶ X := lift 1 1
  have hx₀ : x₀ ≫ f = 1 := by
    rw [show x₀ ≫ f = _ from comp_commutatorMap (𝟙 G.val) i 1 1]
    simp
  have := G.property.1
  have := H.property.1
  have hX : IsAffine X.left := affine_tensor (A := G.val.X) (B := H.val.X)
  have := geometricallyIrreducible_of_connected G
  have := geometricallyIrreducible_of_connected H
  obtain ⟨hXs, hXi⟩ := smooth_geometricallyIrreducible_tensor G.val.X H.val.X
  have hpow (m : ℕ) : IsIntegral (power X m).left := by
    obtain ⟨hs, hir⟩ := power_geometry X m
    exact (geometry_of_smooth_geometricallyIrreducible (power X m)).2.2
  obtain ⟨N, n, w, _, hn, hdom, hf, hmin, hw⟩ :=
    FiniteWordClosure.existsFiniteWordClosure G X f x₀ hX inferInstance inferInstance
      hx₀ hpow (commutatorMap_conjugationStable i hi)
  have hN : IsNormalClosure f N := ⟨hn, hf, fun E _ hE ↦ hmin E hE⟩
  obtain ⟨e, he⟩ := normalClosure_unique hN hd
  let v := w ≫ e.hom.hom.hom
  have hv : IsSchemeTheoreticallyDominant v.left := by
    change IsSchemeTheoreticallyDominant (w.left ≫ e.hom.hom.hom.left)
    have : IsIso e.hom.hom.hom.left :=
      (Grp.forget (SchemeOver k) ⋙ Over.forget _).map_isIso e.hom
    infer_instance
  have ha : IsAffine (wordDomain X n).left := affine_power (X := X) (2 * n)
  have hW : IsIntegral (wordDomain X n).left := hpow (2 * n)
  have hD := (closedSubgroupAlgebraic G D).property.1
  have hDft := (closedSubgroupAlgebraic G D).property.2.1
  have hDr : IsReduced D.group.X.left := IsSchemeTheoreticallyDominant.isReduced v.left
  refine ⟨n, v, ha, (power_geometry X (2 * n)).1, hv,
    smoothOfReducedOverPerfectField k D.group hDr, ?_⟩
  intro T p
  have he' := congrArg (Grp.forget (SchemeOver k)).map he
  simpa only [v, Category.assoc, ← Functor.map_comp] using
    (show p ≫ w ≫ e.hom.hom.hom ≫ D.inclusion.hom.hom = _ from by
      rw [show e.hom.hom.hom ≫ D.inclusion.hom.hom = N.inclusion.hom.hom from he']
      exact hw T p)

private theorem evaluate_mem {G : GroupScheme k} {X T : SchemeOver k} (f : X ⟶ G.X)
    (S : Subgroup (T ⟶ G.X)) (hf : ∀ q : T ⟶ X, q ≫ f ∈ S) (n : ℕ)
    (p : T ⟶ wordDomain X n) : evaluate f n p ∈ S := by
  induction n with
  | zero => exact S.one_mem
  | succ n ih =>
    exact S.mul_mem (S.mul_mem (hf _) (S.inv_mem (hf _))) (ih _)

/-- For a smooth connected group over an algebraically closed field, the
scheme-theoretic derived subgroup is smooth and connected, with the expected
group of rational points. -/
theorem derivedSubgroupOverAlgClosed : Specs.SchemeDerivedGroup.DerivedSubgroupOverAlgClosed.{u} := by
  intro k _ _ G D hd hsm hconn
  let T := 𝟙_ (SchemeOver k)
  let X := G.val.X ⊗ G.val.X
  let Q := closedSubgroupAlgebraic G D
  have hi : IsNormalSubgroup (𝟙 G.val) := ⟨Specs.subgroupConjugation (𝟙 G.val), by simp⟩
  obtain ⟨n, w, ha, hs, hw, hDs, hword⟩ :=
    commutatorWordClosure G G (𝟙 G.val) hi hsm hconn hsm hconn hd
  have hDc := derivedSubgroup_connected G D hd
  refine ⟨hDs, hDc, le_antisymm ?_ (commutatorSubgroupLe D hd T)⟩
  let C := commutator (T ⟶ G.val.X)
  let j : (T ⟶ D.group.X) →* (T ⟶ G.val.X) :=
    ((yonedaGrp.map D.inclusion).app (op T)).hom
  have haQ := Q.property.1
  have hWft : LocallyOfFiniteType (wordDomain X n).hom := inferInstance
  have hWqc : QuasiCompact (wordDomain X n).hom := inferInstance
  have hwd : IsDominant w.left := inferInstance
  have hQint : IsIntegral Q.val.X.left :=
    WordDomainGeometry.smoothConnectedGroupIntegral Q hDs hDc
  have hall : C.comap j = ⊤ := by
    apply WordDomainGeometry.dominantImageGenerates (wordDomain X n) Q w (C.comap j)
    intro p
    change (p ≫ w) ≫ D.inclusion.hom.hom ∈ C
    rw [Category.assoc, hword T p]
    apply evaluate_mem
    intro q
    rw [comp_commutatorMap_projections]
    exact Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _)
  rintro _ ⟨p, rfl⟩
  have hp : p ∈ C.comap j := hall ▸ Subgroup.mem_top _
  exact hp

/-- Over a perfect field, every term of the lower central series of a smooth
connected affine algebraic group is smooth and connected. -/
theorem lowerCentralSeriesSmoothConnected :
    Specs.SchemeDerivedGroup.LowerCentralSeriesSmoothConnected.{u} := by
  intro k _ _ G n D h hsm hconn
  induction h with
  | zero D hi =>
    have he : IsIso D.inclusion.hom.hom.left :=
      (Grp.forget (SchemeOver k) ⋙ Over.forget _).map_isIso D.inclusion
    refine ⟨?_, lowerCentralSeries_connected G (Specs.SchemeDerivedGroup.LowerCentralSeries.zero D hi)⟩
    rw [← Over.w D.inclusion.hom.hom]
    infer_instance
  | @succ n H prev D hd ih =>
    obtain ⟨hHs, hHc⟩ := ih
    obtain ⟨_, _, _, _, _, hDs, _⟩ :=
      commutatorWordClosure G (closedSubgroupAlgebraic G H) H.inclusion
        (lowerCentralSeries_normal prev) hsm hconn hHs hHc hd
    exact ⟨hDs, lowerCentralSeries_connected G (Specs.SchemeDerivedGroup.LowerCentralSeries.succ prev D hd)⟩

end SchemeDerivedGroup

end

end LinearAlgebraicGroups
