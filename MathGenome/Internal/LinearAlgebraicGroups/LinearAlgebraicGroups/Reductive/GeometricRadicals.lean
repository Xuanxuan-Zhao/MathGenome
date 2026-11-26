import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Reductive.GeometricRadicals
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Multiplicative.CharacterDescent
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Solvable.SchemeDerivedGroup
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Unipotent.ExactOperations
import Mathlib.GroupTheory.Solvable
import Mathlib.Tactic.Group
import Batteries.Tactic.OpenPrivate

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite Topology TopologicalSpace
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

universe u

namespace LinearAlgebraicGroups.GeometricRadicals

open Specs.GeometricRadicals (GeometricGroup IsSmoothConnectedNormal IsRadical IsTrivialSubgroup)
open Specs.SchemeDerivedGroup (IsSubgroupOf DerivedSeries IsSolvable)
open Specs.Unipotent (closedSubgroupAlgebraicGroup IsUnipotent)
open Specs.FiniteWordClosure (power wordDomain evaluate ConjugationStable)
open _root_.LinearAlgebraicGroups.Specs (SubgroupSections IsSchemeKernel)

noncomputable section

variable {k : Type u} [Field k]

abbrev IsUnipotentRadical : Specs.GeometricRadicals.RadicalPredicateType.{u} :=
  @Specs.GeometricRadicals.IsUnipotentRadical

abbrev IsSolvableRadical : Specs.GeometricRadicals.RadicalPredicateType.{u} :=
  @Specs.GeometricRadicals.IsSolvableRadical

abbrev geometricUnipotentRadical : Specs.GeometricRadicals.GeometricRadicalType.{u} :=
  @Specs.GeometricRadicals.geometricUnipotentRadical

abbrev geometricSolvableRadical : Specs.GeometricRadicals.GeometricRadicalType.{u} :=
  @Specs.GeometricRadicals.geometricSolvableRadical

abbrev IsReductive : Specs.GeometricRadicals.GroupPredicateType.{u} :=
  @Specs.GeometricRadicals.IsReductive

abbrev IsSemisimple : Specs.GeometricRadicals.GroupPredicateType.{u} :=
  @Specs.GeometricRadicals.IsSemisimple

abbrev IsSplitReductive : Specs.GeometricRadicals.GroupPredicateType.{u} :=
  @Specs.GeometricRadicals.IsSplitReductive

abbrev IsTorus : Specs.GeometricRadicals.TorusPredicateType.{u} :=
  @Specs.GeometricRadicals.IsTorus

abbrev IsSplitTorus : Specs.GeometricRadicals.TorusPredicateType.{u} :=
  @Specs.GeometricRadicals.IsSplitTorus

abbrev IsMaximalTorus : Specs.GeometricRadicals.MaximalTorusPredicateType.{u} :=
  @Specs.GeometricRadicals.IsMaximalTorus

theorem torusCoordinateComparison : Specs.GeometricRadicals.TorusCoordinateComparison.{u} :=
  fun A ↦ (CharacterDescent.torusOnSchemes A).symm

open private affine_tensor affine_power from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Solvable.FiniteWordClosure
open private power_geometry evaluate_mem from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Solvable.SchemeDerivedGroup
open private geometricallyIrreducible_of_connected smooth_geometricallyIrreducible_tensor
  geometry_of_smooth_geometricallyIrreducible sectionOfClosedPoint sectionOfClosedPoint_apply
  exists_section_lift from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Solvable.WordDomainGeometry
open private isReduced_of_smooth_over_field from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Affine.SmoothnessCriteria
open private unipotent_iff_exists_embedding from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Unipotent.ExactOperations
open private schemeKernel_sections isMonHom_of_comp_closed from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Affine.SchemeImageQuotient

set_option maxHeartbeats 2000000
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

private abbrev sectionsMap {G H : GroupScheme k} (f : G ⟶ H) (T : SchemeOver k) :
    (T ⟶ G.X) →* (T ⟶ H.X) :=
  ((yonedaGrp.map f).app (op T)).hom

private theorem sections_normal {G : GroupScheme k} {H : ClosedSubgroup G}
    (hH : IsNormalSubgroup H.inclusion) (T : SchemeOver k) :
    (SubgroupSections H T).Normal := by
  constructor
  rintro _ ⟨x, rfl⟩ g
  exact normalSubgroup_conjugate_sections hH g x

private theorem factor_closed {G : GroupScheme k} {H N : ClosedSubgroup G}
    {j : H.group ⟶ N.group} (hj : j ≫ N.inclusion = H.inclusion) :
    IsClosedImmersion j.hom.hom.left := by
  have := N.isClosedImmersion
  have : IsClosedImmersion (j.hom.hom.left ≫ N.inclusion.hom.hom.left) := by
    rw [show j.hom.hom.left ≫ N.inclusion.hom.hom.left = H.inclusion.hom.hom.left from
      congrArg (fun f : H.group ⟶ G ↦ f.hom.hom.left) hj]
    exact H.isClosedImmersion
  exact IsClosedImmersion.of_comp_isClosedImmersion _ N.inclusion.hom.hom.left

private theorem factor_normal {G : GroupScheme k} {H N : ClosedSubgroup G}
    (hH : IsNormalSubgroup H.inclusion) {j : H.group ⟶ N.group}
    (hj : j ≫ N.inclusion = H.inclusion) : IsNormalSubgroup j := by
  have := N.isClosedImmersion
  have : Mono N.inclusion.hom.hom := Over.mono_of_mono_left N.inclusion.hom.hom
  let p := fst N.group.X H.group.X
  let x := snd N.group.X H.group.X
  obtain ⟨c, hc⟩ := normalSubgroup_conjugate_sections hH (p ≫ N.inclusion.hom.hom) x
  refine ⟨c, (cancel_mono N.inclusion.hom.hom).mp ?_⟩
  have he : j.hom.hom ≫ N.inclusion.hom.hom = H.inclusion.hom.hom :=
    congrArg (Grp.forget (SchemeOver k)).map hj
  rw [Category.assoc, he, hc]
  simp only [Specs.subgroupConjugation, MonObj.mul_comp, GrpObj.inv_comp, Category.assoc, he]
  rfl

private def productMap {G : GroupScheme k} (H K : ClosedSubgroup G) :
    H.group.X ⊗ K.group.X ⟶ G.X :=
  (fst _ _ ≫ H.inclusion.hom.hom) * (snd _ _ ≫ K.inclusion.hom.hom)

private theorem comp_productMap {G : GroupScheme k} (H K : ClosedSubgroup G)
    {T : SchemeOver k} (x : T ⟶ H.group.X) (y : T ⟶ K.group.X) :
    lift x y ≫ productMap H K = sectionsMap H.inclusion T x * sectionsMap K.inclusion T y := by
  simp only [productMap, MonObj.comp_mul, lift_fst_assoc, lift_snd_assoc]
  rfl

private theorem productMap_mem_sup {G : GroupScheme k} (H K : ClosedSubgroup G)
    {T : SchemeOver k} (p : T ⟶ H.group.X ⊗ K.group.X) :
    p ≫ productMap H K ∈ SubgroupSections H T ⊔ SubgroupSections K T := by
  rw [productMap, MonObj.comp_mul]
  have hH : sectionsMap H.inclusion T (p ≫ fst _ _) ∈ SubgroupSections H T :=
    ⟨p ≫ fst _ _, rfl⟩
  have hK : sectionsMap K.inclusion T (p ≫ snd _ _) ∈ SubgroupSections K T :=
    ⟨p ≫ snd _ _, rfl⟩
  exact Subgroup.mul_mem_sup hH hK

private theorem product_sections_of_mem_sup {G : GroupScheme k} {H K : ClosedSubgroup G}
    (hH : IsNormalSubgroup H.inclusion) {T : SchemeOver k} {p : T ⟶ G.X}
    (hp : p ∈ SubgroupSections H T ⊔ SubgroupSections K T) :
    ∃ (x : T ⟶ H.group.X) (y : T ⟶ K.group.X),
      (x ≫ H.inclusion.hom.hom) * (y ≫ K.inclusion.hom.hom) = p := by
  have := sections_normal hH T
  obtain ⟨_, ⟨x, rfl⟩, _, ⟨y, rfl⟩, hxy⟩ := Subgroup.mem_sup_of_normal_left.mp hp
  exact ⟨x, y, hxy⟩

private theorem productMap_conjugationStable {G : GroupScheme k} {H K : ClosedSubgroup G}
    (hH : IsNormalSubgroup H.inclusion) (hK : IsNormalSubgroup K.inclusion) :
    ConjugationStable (productMap H K) := by
  intro T g p
  let x := p ≫ fst H.group.X K.group.X
  let y := p ≫ snd H.group.X K.group.X
  obtain ⟨x', hx'⟩ := normalSubgroup_conjugate_sections hH g x
  obtain ⟨y', hy'⟩ := normalSubgroup_conjugate_sections hK g y
  refine ⟨lift x' y', ?_⟩
  rw [comp_productMap]
  change (x' ≫ H.inclusion.hom.hom) * (y' ≫ K.inclusion.hom.hom) =
    g * (p ≫ productMap H K) * g⁻¹
  rw [hx', hy', productMap, MonObj.comp_mul]
  change (g * (x ≫ H.inclusion.hom.hom) * g⁻¹) *
    (g * (y ≫ K.inclusion.hom.hom) * g⁻¹) =
      g * ((x ≫ H.inclusion.hom.hom) * (y ≫ K.inclusion.hom.hom)) * g⁻¹
  group

/-- The smooth connected normal product has a schematically dominant multiplication map. -/
private theorem exists_product [IsAlgClosed k] (G : AffineAlgebraicGroup k)
    (H K : ClosedSubgroup G.val) (hH : IsSmoothConnectedNormal H) (hK : IsSmoothConnectedNormal K) :
    ∃ (N : ClosedSubgroup G.val) (j : H.group ⟶ N.group) (l : K.group ⟶ N.group),
      IsSmoothConnectedNormal N ∧ j ≫ N.inclusion = H.inclusion ∧ l ≫ N.inclusion = K.inclusion ∧
      IsSchemeTheoreticallyDominant
        (((fst H.group.X K.group.X) ≫ j.hom.hom) *
          ((snd H.group.X K.group.X) ≫ l.hom.hom)).left := by
  let A := closedSubgroupAlgebraicGroup H
  let B := closedSubgroupAlgebraicGroup K
  let X := H.group.X ⊗ K.group.X
  let f := productMap H K
  have hHA : IsAffine H.group.X.left := A.property.1
  have hHB : IsAffine K.group.X.left := B.property.1
  have hAf : LocallyOfFiniteType H.group.X.hom := A.property.2.1
  have hBf : LocallyOfFiniteType K.group.X.hom := B.property.2.1
  have hAq : QuasiCompact H.group.X.hom := A.property.2.2
  have hBq : QuasiCompact K.group.X.hom := B.property.2.2
  have hXa : IsAffine X.left := affine_tensor (A := H.group.X) (B := K.group.X)
  have : Smooth H.group.X.hom := hH.1
  have : Smooth K.group.X.hom := hK.1
  have : ConnectedSpace A.val.X.left := hH.2.1
  have : ConnectedSpace B.val.X.left := hK.2.1
  have : GeometricallyIrreducible H.group.X.hom := geometricallyIrreducible_of_connected A
  have : GeometricallyIrreducible K.group.X.hom := geometricallyIrreducible_of_connected B
  obtain ⟨hXs, hXi⟩ := smooth_geometricallyIrreducible_tensor H.group.X K.group.X
  have hpow (m : ℕ) : IsIntegral (power X m).left := by
    obtain ⟨hs, hi⟩ := power_geometry X m
    exact (geometry_of_smooth_geometricallyIrreducible (power X m)).2.2
  let x₀ : 𝟙_ (SchemeOver k) ⟶ X := lift 1 1
  have hx₀ : x₀ ≫ f = 1 := by
    change lift 1 1 ≫ productMap H K = _
    rw [comp_productMap, map_one, map_one, one_mul]
  obtain ⟨N, n, w, _, hn, hd, ⟨fN, hfN⟩, _, hw⟩ :=
    FiniteWordClosure.existsFiniteWordClosure G X f x₀ inferInstance inferInstance inferInstance
      hx₀ hpow (productMap_conjugationStable hH.2.2 hK.2.2)
  have hNft : LocallyOfFiniteType N.group.X.hom := (closedSubgroupAlgebraicGroup N).property.2.1
  have hW : IsIntegral (wordDomain X n).left := hpow (2 * n)
  have hWa : IsAffine (wordDomain X n).left := affine_power (2 * n)
  have hNa : IsAffine N.group.X.left := (closedSubgroupAlgebraicGroup N).property.1
  have hr : IsReduced N.group.X.left := IsSchemeTheoreticallyDominant.isReduced w.left
  have hs : Smooth N.group.X.hom := smoothOfReducedOverPerfectField k N.group hr
  have hc : ConnectedSpace N.group.X.left :=
    { toPreconnectedSpace := w.left.denseRange.preconnectedSpace w.left.continuous
      toNonempty := ⟨(1 : (𝟙_ (SchemeOver k)) ⟶ N.group.X).left
        (IsLocalRing.closedPoint k)⟩ }
  have := N.isClosedImmersion
  have hm : Mono N.inclusion.hom.hom := Over.mono_of_mono_left N.inclusion.hom.hom
  let j₀ := lift (𝟙 H.group.X) (1 : H.group.X ⟶ K.group.X) ≫ fN
  let l₀ := lift (1 : K.group.X ⟶ H.group.X) (𝟙 K.group.X) ≫ fN
  have hj₀ : j₀ ≫ N.inclusion.hom.hom = H.inclusion.hom.hom := by
    rw [Category.assoc, hfN, comp_productMap, map_one, mul_one]
    change 𝟙 H.group.X ≫ H.inclusion.hom.hom = _
    simp
  have hl₀ : l₀ ≫ N.inclusion.hom.hom = K.inclusion.hom.hom := by
    rw [Category.assoc, hfN, comp_productMap, map_one, one_mul]
    change 𝟙 K.group.X ≫ K.inclusion.hom.hom = _
    simp
  have hjmon : IsMonHom j₀ := isMonHom_of_comp_closed
    j₀ H.inclusion N.inclusion hj₀
  have hlmon : IsMonHom l₀ := isMonHom_of_comp_closed
    l₀ K.inclusion N.inclusion hl₀
  let j := Grp.homMk j₀
  let l := Grp.homMk l₀
  refine ⟨N, j, l, ⟨hs, hc, hn⟩, Grp.hom_ext _ _ hj₀, Grp.hom_ext _ _ hl₀, ?_⟩
  have hf : ((fst H.group.X K.group.X ≫ j₀) * (snd H.group.X K.group.X ≫ l₀)) = fN := by
    apply (cancel_mono N.inclusion.hom.hom).mp
    rw [MonObj.mul_comp, Category.assoc (fst _ _) j₀, Category.assoc (snd _ _) l₀,
      hj₀, hl₀, hfN]
    rfl
  change IsSchemeTheoreticallyDominant
    (((fst H.group.X K.group.X ≫ j₀) * (snd H.group.X K.group.X ≫ l₀))).left
  rw [hf]
  -- Any signed word in the two factors lies in their setwise product.
  let T := wordDomain X n
  let S := SubgroupSections H T ⊔ SubgroupSections K T
  have hword : evaluate f n (𝟙 T) ∈ S :=
    evaluate_mem f S (productMap_mem_sup H K) n (𝟙 T)
  obtain ⟨x, y, hxy⟩ := product_sections_of_mem_sup hH.2.2 hword
  have hw' : w = lift x y ≫ fN := by
    apply (cancel_mono N.inclusion.hom.hom).mp
    rw [Category.assoc, hfN, comp_productMap]
    change w ≫ N.inclusion.hom.hom = (x ≫ H.inclusion.hom.hom) * (y ≫ K.inclusion.hom.hom)
    have he : w ≫ N.inclusion.hom.hom = evaluate f n (𝟙 T) := by
      simpa only [Category.id_comp] using hw T (𝟙 T)
    exact he.trans hxy.symm
  have hdom : IsSchemeTheoreticallyDominant ((lift x y).left ≫ fN.left) := by
    change IsSchemeTheoreticallyDominant (lift x y ≫ fN).left
    rw [← hw']
    exact hd
  exact ⟨bot_unique (((lift x y).left.le_ker_comp fN.left).trans_eq hdom.ker_eq_bot)⟩

private abbrev rationalSections (G : GroupScheme k) :=
  (𝟙_ (SchemeOver k)) ⟶ G.X

private abbrev rationalMap {G H : GroupScheme k} (f : G ⟶ H) :
    rationalSections G →* rationalSections H :=
  sectionsMap f (𝟙_ (SchemeOver k))

/-- The successive scheme-derived groups have the corresponding ordinary derived groups
as their images on rational points. -/
private theorem derivedSeries_sections [IsAlgClosed k] (G : AffineAlgebraicGroup k)
    (hs : Smooth G.val.X.hom) (hc : ConnectedSpace G.val.X.left)
    {n : ℕ} {H : GroupScheme k} (h : DerivedSeries G.val n H) :
    ∃ (i : H ⟶ G.val) (_ : IsClosedImmersion i.hom.hom.left),
      Smooth H.X.hom ∧ ConnectedSpace H.X.left ∧
      (rationalMap i).range = derivedSeries (rationalSections G.val) n := by
  induction h with
  | zero =>
    refine ⟨𝟙 G.val, inferInstanceAs (IsClosedImmersion (𝟙 G.val.X.left)), hs, hc, ?_⟩
    rw [derivedSeries_zero]
    apply MonoidHom.range_eq_top.mpr
    intro p
    refine ⟨p, ?_⟩
    change p ≫ 𝟙 G.val.X = p
    simp
  | @succ n H prev D hD ih =>
    obtain ⟨i, hi, hHs, hHc, hr⟩ := ih
    let I : ClosedSubgroup G.val := ⟨H, i, hi⟩
    let A := closedSubgroupAlgebraicGroup I
    obtain ⟨hDs, hDc, hDr⟩ := SchemeDerivedGroup.derivedSubgroupOverAlgClosed A D hD hHs hHc
    let hd := D.isClosedImmersion
    refine ⟨D.inclusion ≫ i, inferInstanceAs
      (IsClosedImmersion (D.inclusion.hom.hom.left ≫ i.hom.hom.left)), hDs, hDc, ?_⟩
    change (rationalMap D.inclusion).range = commutator (rationalSections H) at hDr
    change ((rationalMap i).comp (rationalMap D.inclusion)).range = _
    rw [MonoidHom.range_comp, hDr, map_commutator_eq, hr, derivedSeries_succ]

private theorem isIso_of_schemeIso {G H : GroupScheme k} (f : G ⟶ H)
    [IsIso f.hom.hom.left] : IsIso f := by
  have h : IsIso ((Over.forget (Spec (CommRingCat.of k))).map f.hom.hom) :=
    inferInstanceAs (IsIso f.hom.hom.left)
  have : IsIso f.hom.hom := isIso_of_reflects_iso _ (Over.forget _)
  let e : G ≅ H := Grp.mkIso (asIso f.hom.hom) (IsMonHom.one_hom (f := f.hom.hom))
    (IsMonHom.mul_hom (f := f.hom.hom))
  have he : e.hom = f := Grp.hom_ext _ _ rfl
  exact he ▸ (inferInstance : IsIso e.hom)

private theorem trivial_of_subsingleton_sections [IsAlgClosed k] (G : AffineAlgebraicGroup k)
    (hs : Smooth G.val.X.hom) [Subsingleton (rationalSections G.val)] :
    Nonempty (G.val ≅ Grp.trivial (SchemeOver k)) := by
  let e := Specs.GeometricRadicals.identitySubgroup G
  have hGa := G.property.1
  have hGf := G.property.2.1
  have := hs
  have hGr : IsReduced G.val.X.left := isReduced_of_smooth_over_field G.val.X.hom
  have hJac : JacobsonSpace G.val.X.left := LocallyOfFiniteType.jacobsonSpace G.val.X.hom
  have hi := e.isClosedImmersion
  have hsurj : Surjective e.inclusion.hom.hom.left := by
    constructor
    have hc : closedPoints G.val.X.left ⊆ Set.range e.inclusion.hom.hom.left := by
      intro x hx
      let s := sectionOfClosedPoint G.val.X x hx
      let p : rationalSections G.val := (𝟙 (𝟙_ (SchemeOver k))) ≫ e.inclusion.hom.hom
      have hp : p = s := Subsingleton.elim _ _
      refine ⟨IsLocalRing.closedPoint k, ?_⟩
      change p.left (IsLocalRing.closedPoint k) = x
      rw [hp, sectionOfClosedPoint_apply]
    have hcl := hi.isClosedEmbedding.isClosed_range.closure_subset_iff.mpr hc
    rw [closure_closedPoints] at hcl
    exact Set.range_eq_univ.mp (Set.Subset.antisymm (Set.subset_univ _) hcl)
  have hi' : IsIso e.inclusion.hom.hom.left :=
    isIso_of_isClosedImmersion_of_surjective _
  have : IsIso e.inclusion := isIso_of_schemeIso _
  exact ⟨(asIso e.inclusion).symm⟩

private theorem solvable_iff_sections [IsAlgClosed k] (G : AffineAlgebraicGroup k)
    (hs : Smooth G.val.X.hom) (hc : ConnectedSpace G.val.X.left) :
    IsSolvable G.val ↔ Group.IsSolvable (rationalSections G.val) := by
  constructor
  · rintro ⟨n, H, hd, ⟨e⟩⟩
    obtain ⟨i, _, _, _, hi⟩ := derivedSeries_sections G hs hc hd
    have hm : Mono e.hom.hom.hom := inferInstance
    refine ⟨n, hi ▸ le_antisymm ?_ bot_le⟩
    rintro p ⟨q, rfl⟩
    rw [Subgroup.mem_bot]
    have hq : q = 1 := (cancel_mono e.hom.hom.hom).mp
      ((isTerminalTensorUnit (C := SchemeOver k)).hom_ext _ _)
    rw [hq, map_one]
  · rintro ⟨n, hn⟩
    obtain ⟨H, hH⟩ := SchemeDerivedGroup.derivedSeriesExists G n
    obtain ⟨i, hi, hHs, _, hr⟩ := derivedSeries_sections G hs hc hH
    have hm : Mono i.hom.hom := Over.mono_of_mono_left i.hom.hom
    have hq (q : rationalSections H.val) : rationalMap i q = 1 := by
      exact Subgroup.mem_bot.mp ((hr.trans hn) ▸ (show rationalMap i q ∈ (rationalMap i).range
        from ⟨q, rfl⟩))
    have hsub : Subsingleton (rationalSections H.val) := ⟨fun a b ↦
      (cancel_mono i.hom.hom).mp ((hq a).trans (hq b).symm)⟩
    exact ⟨n, H.val, hH, trivial_of_subsingleton_sections H hHs⟩

/-- In the product of two smooth connected normal subgroups, the quotient by the
first factor is a faithfully flat image of the second. -/
private theorem product_quotient {G : AffineAlgebraicGroup k}
    {H K N : ClosedSubgroup G.val} (hH : IsNormalSubgroup H.inclusion)
    (j : H.group ⟶ N.group) (l : K.group ⟶ N.group)
    (hj : j ≫ N.inclusion = H.inclusion)
    (hd : IsSchemeTheoreticallyDominant
      (((fst H.group.X K.group.X) ≫ j.hom.hom) * ((snd H.group.X K.group.X) ≫ l.hom.hom)).left) :
    ∃ (J : ClosedSubgroup N.group) (Q : AffineAlgebraicGroup k) (q : N.group ⟶ Q.val),
      J.group = H.group ∧
      IsSchemeKernel q J ∧ Flat q.hom.hom.left ∧ Surjective q.hom.hom.left ∧
      Flat (l ≫ q).hom.hom.left ∧ Surjective (l ≫ q).hom.hom.left := by
  let C := closedSubgroupAlgebraicGroup N
  let J : ClosedSubgroup N.group := ⟨H.group, j, factor_closed hj⟩
  obtain ⟨_, _, Q, q, _, _, hker, hqi, _, _⟩ :=
    normalAffineQuotient C J (factor_normal hH hj)
  have hQa : IsAffine Q.val.X.left := Q.property.1
  have hCa : IsAffine N.group.X.left := C.property.1
  have hCaf : IsAffine C.val.toMon.X.left := C.property.1
  have hKa : IsAffine K.group.X.left := (closedSubgroupAlgebraicGroup K).property.1
  have hHa : IsAffine H.group.X.left := (closedSubgroupAlgebraicGroup H).property.1
  let X := H.group.X ⊗ K.group.X
  have hXa : IsAffine X.left := affine_tensor (A := H.group.X) (B := K.group.X)
  let f : X ⟶ N.group.X := (fst _ _ ≫ j.hom.hom) * (snd _ _ ≫ l.hom.hom)
  have hfi : Function.Injective f.left.appTop := f.left.app_injective ⊤
  have hqinj : Function.Injective q.hom.hom.left.appTop :=
    ((Flat.flat_and_surjective_iff_faithfullyFlat_of_isAffine _).mp ⟨hqi.2.1, hqi.2.2.1⟩).injective
  have heq : f ≫ q.hom.hom = snd H.group.X K.group.X ≫ (l ≫ q).hom.hom := by
    have hkill : (fst H.group.X K.group.X ≫ j.hom.hom) ≫ q.hom.hom = 1 :=
      (schemeKernel_sections hker _).mp ⟨fst _ _, rfl⟩
    dsimp only [f]
    rw [MonObj.mul_comp, hkill, one_mul, Category.assoc]
    rfl
  have hc : f.left ≫ q.hom.hom.left =
      (snd H.group.X K.group.X).left ≫ (l ≫ q).hom.hom.left :=
    congrArg (fun a : X ⟶ Q.val.X ↦ a.left) heq
  have hinj : Function.Injective (l ≫ q).hom.hom.left.appTop := by
    have h : Function.Injective ((f.left ≫ q.hom.hom.left).appTop) := by
      rw [Scheme.Hom.comp_appTop]
      exact hfi.comp hqinj
    rw [hc, Scheme.Hom.comp_appTop] at h
    change Function.Injective ((snd H.group.X K.group.X).left.appTop ∘
      (l ≫ q).hom.hom.left.appTop) at h
    exact h.of_comp
  obtain ⟨I, p, i, hi, _, _⟩ := schemeImageFactorization (closedSubgroupAlgebraicGroup K) Q (l ≫ q)
  have hI : IsClosedImmersion i.hom.hom.left := hi.2.2.2.2.2
  have hpq : p.hom.hom.left ≫ i.hom.hom.left = (l ≫ q).hom.hom.left :=
    congrArg (fun a : K.group ⟶ Q.val ↦ a.hom.hom.left) hi.1
  have hii : Function.Injective i.hom.hom.left.appTop := by
    rw [← hpq, Scheme.Hom.comp_appTop] at hinj
    change Function.Injective (p.hom.hom.left.appTop ∘ i.hom.hom.left.appTop) at hinj
    exact hinj.of_comp
  have hiso : IsIso i.hom.hom.left := IsClosedImmersion.isIso_of_injective_of_isAffine hii
  refine ⟨J, Q, q, rfl, hker, hqi.2.1, hqi.2.2.1, ?_, ?_⟩
  · rw [← hpq]
    have := hi.2.1
    infer_instance
  · rw [← hpq]
    have := hi.2.2.1
    infer_instance

private theorem unipotent_product {G : AffineAlgebraicGroup k} {H K N : ClosedSubgroup G.val}
    (hH : IsNormalSubgroup H.inclusion)
    (j : H.group ⟶ N.group) (l : K.group ⟶ N.group)
    (hj : j ≫ N.inclusion = H.inclusion)
    (hd : IsSchemeTheoreticallyDominant
      (((fst H.group.X K.group.X) ≫ j.hom.hom) * ((snd H.group.X K.group.X) ≫ l.hom.hom)).left)
    (huH : IsUnipotent (closedSubgroupAlgebraicGroup H))
    (huK : IsUnipotent (closedSubgroupAlgebraicGroup K)) :
    IsUnipotent (closedSubgroupAlgebraicGroup N) := by
  obtain ⟨J, Q, q, hJ, hker, hqf, hqs, hlf, hls⟩ := product_quotient hH j l hj hd
  have hQ := Unipotent.faithfullyFlatQuotientsUnipotent (closedSubgroupAlgebraicGroup K) Q
    (l ≫ q) hlf hls huK
  refine Unipotent.extensionsUnipotent (closedSubgroupAlgebraicGroup N) Q q J hker hqf hqs ?_ hQ
  have he : closedSubgroupAlgebraicGroup (G := closedSubgroupAlgebraicGroup N) J =
      closedSubgroupAlgebraicGroup H := Subtype.ext hJ
  exact he ▸ huH

private theorem solvable_product [IsAlgClosed k] {G : AffineAlgebraicGroup k}
    {H K N : ClosedSubgroup G.val} (hH : IsSmoothConnectedNormal H)
    (hK : IsSmoothConnectedNormal K) (hN : IsSmoothConnectedNormal N)
    (j : H.group ⟶ N.group) (l : K.group ⟶ N.group)
    (hj : j ≫ N.inclusion = H.inclusion)
    (hd : IsSchemeTheoreticallyDominant
      (((fst H.group.X K.group.X) ≫ j.hom.hom) * ((snd H.group.X K.group.X) ≫ l.hom.hom)).left)
    (hsH : IsSolvable H.group) (hsK : IsSolvable K.group) :
    IsSolvable N.group := by
  let C := closedSubgroupAlgebraicGroup N
  have hC := C.property.2.1
  have : Group.IsSolvable (rationalSections H.group) :=
    (solvable_iff_sections (closedSubgroupAlgebraicGroup H) hH.1 hH.2.1).mp hsH
  have : Group.IsSolvable (rationalSections K.group) :=
    (solvable_iff_sections (closedSubgroupAlgebraicGroup K) hK.1 hK.2.1).mp hsK
  obtain ⟨J, Q, q, hJ, hker, _, _, _, hls⟩ := product_quotient hH.2.2 j l hj hd
  have hKft : LocallyOfFiniteType K.group.toMon.X.hom :=
    (closedSubgroupAlgebraicGroup K).property.2.1
  have hQft := Q.property.2.1
  have hsurj : Function.Surjective (rationalMap (l ≫ q)) := fun p ↦
    exists_section_lift (l ≫ q).hom.hom p (hls.surj _)
  have : Group.IsSolvable (rationalSections Q.val) := Group.isSolvable_of_surjective hsurj
  have hker' : (rationalMap q).ker ≤ (rationalMap J.inclusion).range :=
    fun p hp ↦ (schemeKernel_sections hker p).mpr hp
  have hJs : Group.IsSolvable (rationalSections J.group) := hJ ▸
    (inferInstance : Group.IsSolvable (rationalSections H.group))
  exact (solvable_iff_sections C hN.1 hN.2.1).mpr
    (Group.isSolvable_of_ker_le_range (rationalMap J.inclusion) (rationalMap q) hker')

private theorem identity_smoothConnectedNormal (G : AffineAlgebraicGroup k) :
    IsSmoothConnectedNormal (Specs.GeometricRadicals.identitySubgroup G) := by
  let E := Specs.GeometricRadicals.identitySubgroup G
  have hs : Smooth E.group.X.hom := inferInstanceAs (Smooth (𝟙 (Spec (CommRingCat.of k))))
  have hc : ConnectedSpace E.group.X.left :=
    inferInstanceAs (ConnectedSpace (Spec (CommRingCat.of k)))
  refine ⟨hs, hc, toUnit _, ?_⟩
  change (1 : G.val.X ⊗ E.group.X ⟶ G.val.X) =
    fst G.val.X E.group.X * (snd G.val.X E.group.X ≫ η[G.val.X]) *
      (fst G.val.X E.group.X)⁻¹
  rw [MonObj.one_eq_one, MonObj.comp_one, mul_one, mul_inv_cancel]

private theorem identity_unipotent (G : AffineAlgebraicGroup k) :
    IsUnipotent (closedSubgroupAlgebraicGroup (Specs.GeometricRadicals.identitySubgroup G)) := by
  let U := Unipotent.unitriangularGroup k 0
  have hU := U.property.1
  let j : Grp.trivial (SchemeOver k) ⟶ U.val :=
    (Specs.GeometricRadicals.identitySubgroup U).inclusion
  exact (unipotent_iff_exists_embedding _).mpr
    ⟨0, U, ⟨Unipotent.unitriangularGroupPointsIso k 0⟩, j,
      (Specs.GeometricRadicals.identitySubgroup U).isClosedImmersion⟩

private theorem identity_solvable (G : AffineAlgebraicGroup k) :
    IsSolvable (Specs.GeometricRadicals.identitySubgroup G).group :=
  ⟨0, _, DerivedSeries.zero, ⟨Iso.refl _⟩⟩

private abbrev definingIdeal {G : AffineAlgebraicGroup k} (H : ClosedSubgroup G.val) :
    Ideal Γ(G.val.X.left, ⊤) :=
  RingHom.ker H.inclusion.hom.hom.left.appTop.hom

private theorem definingIdeal_prime [IsAlgClosed k] {G : AffineAlgebraicGroup k}
    {H : ClosedSubgroup G.val} (hH : IsSmoothConnectedNormal H) :
    (definingIdeal H).IsPrime := by
  have h : IsIntegral H.group.X.left := WordDomainGeometry.smoothConnectedGroupIntegral
    (closedSubgroupAlgebraicGroup H) hH.1 hH.2.1
  have hD : IsDomain Γ(H.group.X.left, ⊤) := inferInstance
  exact RingHom.ker_isPrime _

private theorem definingIdeal_le {G : AffineAlgebraicGroup k} {H N : ClosedSubgroup G.val}
    (j : H.group ⟶ N.group) (hj : j ≫ N.inclusion = H.inclusion) :
    definingIdeal N ≤ definingIdeal H := by
  have he : j.hom.hom.left ≫ N.inclusion.hom.hom.left = H.inclusion.hom.hom.left :=
    congrArg (fun f : H.group ⟶ G.val ↦ f.hom.hom.left) hj
  intro x hx
  change H.inclusion.hom.hom.left.appTop x = 0
  change N.inclusion.hom.hom.left.appTop x = 0 at hx
  rw [← he, Scheme.Hom.comp_appTop, CommRingCat.comp_apply, hx, map_zero]

private theorem factor_iso_of_definingIdeal_eq {G : AffineAlgebraicGroup k}
    {H N : ClosedSubgroup G.val} (j : H.group ⟶ N.group)
    (hj : j ≫ N.inclusion = H.inclusion) (hI : definingIdeal H = definingIdeal N) :
    IsIso j := by
  have hG := G.property.1
  have hi := H.isClosedImmersion
  have hn := N.isClosedImmersion
  have he : j.hom.hom.left ≫ N.inclusion.hom.hom.left = H.inclusion.hom.hom.left :=
    congrArg (fun f : H.group ⟶ G.val ↦ f.hom.hom.left) hj
  have hker : H.inclusion.hom.hom.left.ker = N.inclusion.hom.hom.left.ker := by
    rw [Scheme.ker_of_isAffine, Scheme.ker_of_isAffine]
    exact congrArg Scheme.IdealSheafData.ofIdealTop hI
  have : IsIso j.hom.hom.left :=
    IsClosedImmersion.isIso_of_ker_eq _ _ _ he hker
  exact isIso_of_schemeIso j

/-- Select a subgroup of minimum prime height in the Noetherian ambient coordinate ring. -/
private theorem radical_exists [IsAlgClosed k] (G : AffineAlgebraicGroup k)
    (P : AffineAlgebraicGroup k → Prop)
    (h₀ : P (closedSubgroupAlgebraicGroup (Specs.GeometricRadicals.identitySubgroup G)))
    (hprod : ∀ {H K N : ClosedSubgroup G.val}, IsSmoothConnectedNormal H →
      IsSmoothConnectedNormal K → IsSmoothConnectedNormal N →
      ∀ (j : H.group ⟶ N.group) (l : K.group ⟶ N.group),
        j ≫ N.inclusion = H.inclusion →
        IsSchemeTheoreticallyDominant
          (((fst H.group.X K.group.X) ≫ j.hom.hom) * ((snd H.group.X K.group.X) ≫ l.hom.hom)).left →
        P (closedSubgroupAlgebraicGroup H) → P (closedSubgroupAlgebraicGroup K) →
        P (closedSubgroupAlgebraicGroup N)) :
    ∃ N : ClosedSubgroup G.val, IsRadical G P N := by
  classical
  have hGa := G.property.1
  have hGf := G.property.2.1
  have hGn : IsLocallyNoetherian G.val.X.left := LocallyOfFiniteType.isLocallyNoetherian G.val.X.hom
  have : IsNoetherianRing Γ(G.val.X.left, ⊤) :=
    hGn.component_noetherian ⟨⊤, isAffineOpen_top G.val.X.left⟩
  let score (N : ClosedSubgroup G.val) : ℕ := (definingIdeal N).height.toNat
  let eligible (n : ℕ) := ∃ H : ClosedSubgroup G.val, IsSmoothConnectedNormal H ∧
    P (closedSubgroupAlgebraicGroup H) ∧ score H = n
  have hex : ∃ n, eligible n :=
    ⟨_, _, identity_smoothConnectedNormal G, h₀, rfl⟩
  obtain ⟨H, hH, hpH, hscore⟩ := Nat.find_spec hex
  refine ⟨H, hH, hpH, ?_⟩
  intro K hK hpK
  obtain ⟨N, j, l, hN, hj, hl, hd⟩ := exists_product G H K hH hK
  have hpN := hprod hH hK hN j l hj hd hpH hpK
  have hmin : score H ≤ score N := hscore ▸ Nat.find_min' hex ⟨N, hN, hpN, rfl⟩
  have hle := definingIdeal_le j hj
  have hI : definingIdeal H = definingIdeal N := by
    by_contra hne
    have hHpri : (definingIdeal H).IsPrime := definingIdeal_prime hH
    have hNpri : (definingIdeal N).IsPrime := definingIdeal_prime hN
    have hlt := Ideal.height_strict_mono_of_isPrime_of_isPrime (lt_of_le_of_ne hle (fun he ↦ hne he.symm))
    have hlt' : score N < score H := by
      have eqN := ENat.natCast_toNat (Ideal.height_ne_top_of_isPrime (I := definingIdeal N))
      have eqH := ENat.natCast_toNat (Ideal.height_ne_top_of_isPrime (I := definingIdeal H))
      exact ENat.natCast_lt_natCast.mp (eqN.symm ▸ eqH.symm ▸ hlt)
    exact (not_lt_of_ge hmin) hlt'
  have : IsIso j := factor_iso_of_definingIdeal_eq j hj hI
  refine ⟨l ≫ inv j, ?_⟩
  have he : inv j ≫ H.inclusion = N.inclusion := by rw [← hj, IsIso.inv_hom_id_assoc]
  rw [Category.assoc, he, hl]

theorem unipotentRadicalExists : Specs.GeometricRadicals.UnipotentRadicalExists.{u} := by
  intro k _ _ G
  exact radical_exists G IsUnipotent (identity_unipotent G)
    (fun hH _ _ j l hj hd ↦ unipotent_product hH.2.2 j l hj hd)

theorem solvableRadicalExists : Specs.GeometricRadicals.SolvableRadicalExists.{u} := by
  intro k _ _ G
  exact radical_exists G (fun H ↦ IsSolvable H.val) (identity_solvable G) solvable_product

theorem radicalUnique : Specs.GeometricRadicals.RadicalUnique.{u} := by
  intro k _ G P H N hH hN
  obtain ⟨i, hi⟩ := hN.2.2 H hH.1 hH.2.1
  obtain ⟨j, hj⟩ := hH.2.2 N hN.1 hN.2.1
  let F := Grp.forget (SchemeOver k) ⋙ Over.forget (Spec (CommRingCat.of k))
  have hcH : IsClosedImmersion (F.map H.inclusion) := H.isClosedImmersion
  have hcN : IsClosedImmersion (F.map N.inclusion) := N.isClosedImmersion
  have hmH : Mono H.inclusion := F.mono_of_mono_map inferInstance
  have hmN : Mono N.inclusion := F.mono_of_mono_map inferInstance
  let e : H.group ≅ N.group :=
    ⟨i, j, (cancel_mono H.inclusion).mp (by rw [Category.assoc, hj, hi, Category.id_comp]),
      (cancel_mono N.inclusion).mp (by rw [Category.assoc, hi, hj, Category.id_comp])⟩
  exact ⟨e, hi, fun d hd ↦ Iso.ext ((cancel_mono N.inclusion).mp (hd.trans hi.symm))⟩

theorem geometricUnipotentRadicalLargest :
    Specs.GeometricRadicals.GeometricUnipotentRadicalLargest.{u} := by
  intro k _ G
  exact Classical.epsilon_spec (unipotentRadicalExists (GeometricGroup G))

theorem geometricSolvableRadicalLargest :
    Specs.GeometricRadicals.GeometricSolvableRadicalLargest.{u} := by
  intro k _ G
  exact Classical.epsilon_spec (solvableRadicalExists (GeometricGroup G))

end
end LinearAlgebraicGroups.GeometricRadicals
